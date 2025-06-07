import getpass
import json
import subprocess
import os
import re
import platform

def build_invariant(index, inv, type_names):
    trace_var = "Trace"
    actions = inv["sequence"]
    last = actions[-1]
    preconds = actions[:-1]
    datatype = inv["type"]

    name = f"Invariant{index+1}"
    comment = inv["description"]

    # Автоматически определяем имя функции проверки типа
    def format_typename(t):
        return "Is" + t.lower().capitalize()

    if datatype.lower() not in type_names:
        raise ValueError(f"Тип '{datatype}' не найден среди доступных типов: {type_names}")

    type_check = format_typename(datatype)

    # если действие произошло в текущем состоянии
    head = f'("{last}" \\in PropertyMap[{trace_var}[i]] /\\ {type_check}({trace_var}[i]))'

    # то действия должны были произойти раньше
    body = " /\\\n      ".join([
        f'\\E j{n} \\in 1..(i-1) : "{act}" \\in PropertyMap[{trace_var}[j{n}]] /\\ {type_check}({trace_var}[j{n}])'
        for n, act in enumerate(preconds, start=1)
    ])

    formula = f"""\n(* {comment} *)
{name} ==
  \\A i \\in 1..Len({trace_var}) :
    {head} =>
      {body}"""

    return name, formula

# автоматическое считывание типов из графа
def extract_type_checks(prop_map):
    type_set = set()

    for props in prop_map.values():
        for p in props:
            if p.startswith("type="):
                type_set.add(p.split("=")[1])

    checks = []
    for t in sorted(type_set):
        func = f'Is{t.capitalize()}(s) == "type={t}" \\in PropertyMap[s]'
        checks.append(func)
    return checks

# выписывание инвариантов
def print_invariants(json_path="invariants_kripke.json"):
    try:
        with open(json_path, "r", encoding="utf-8") as f:
            invariants = json.load(f)

        print("\nПроверяемые инварианты:\n")
        for idx, inv in enumerate(invariants, start=1):
            print(f"{idx}. {inv['description']}")

    except Exception as e:
        print(f"Ошибка при чтении {json_path}: {e}")


# Генерация спецификации
def generate_tla_spec(graph_path: str, invariants_path: str, tla_path: str = "main.tla"):
    with open(graph_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    with open(invariants_path, "r", encoding="utf-8") as f:
        inv_data = json.load(f)

    states = [f"S{node['id']}" for node in data["nodes"]]
    edges = []
    prop_map = {}

    for node in data["nodes"]:
        sid = f"S{node['id']}"
        prop_map[sid] = set(node.get("properties", []))
        for target in node.get("outgoing_edges", []):
            tid = f"S{target}"
            edges.append(f'<<"{sid}", "{tid}">>')

    def format_properties(prop_set):
        return "{" + ", ".join(f'"{p}"' for p in sorted(prop_set)) + "}"

    with open(tla_path, "w", encoding="utf-8") as f:
        f.write(f"""------------------------------- MODULE main -------------------------------
EXTENDS Sequences, TLC, FiniteSets, Integers

VARIABLES Trace

States == {{{", ".join(f'"{s}"' for s in states)}}}

Edges == {{
  {", ".join(edges)}
}}

PropertyMap == [
""")
        last_idx = len(states) - 1
        for idx, sid in enumerate(states):
            line = f'  {sid} |-> {format_properties(prop_map.get(sid, set()))}'
            if idx != last_idx:
                line += ","
            f.write(line + "\n")
        f.write("]\n")

        type_checks = extract_type_checks(prop_map)
        type_names = set()
        for props in prop_map.values():
            for p in props:
                if p.startswith("type="):
                    type_names.add(p.split("=")[1])

        f.write("\n" + "\n".join(type_checks) + "\n")

        f.write('Init == Trace = << "S0" >>\n')

        f.write("""
        Next ==
          \\E t \\in States :
            /\\ <<Trace[Len(Trace)], t>> \\in Edges
            /\\ ~(\\E i \\in 1..Len(Trace) : Trace[i] = t)
            /\\ Trace' = Trace \\o <<t>>""")

        invariant_defs = []
        invariant_names = []

        for idx, inv in enumerate(inv_data):
            name, formula = build_invariant(idx, inv, type_names)
            invariant_names.append(name)
            invariant_defs.append(formula)

        f.write("\n" + "\n".join(invariant_defs))
        f.write(f"\n\nAllInvariants == " + " /\\ ".join(invariant_names))
        f.write("""




Spec == Init /\\ [][Next]_<<Trace>>

THEOREM Spec => <>[]AllInvariants

==============================================================================
""")

# Генерация конфиг. файлов
def generate_mc_files(mc_tla_path, mc_cfg_path):
    tla_mc_content = f"""
---- MODULE MC ----
EXTENDS main, TLC

\* PROPERTY definition @modelCorrectnessProperties:0
prop_main ==
<>[]AllInvariants
----
=============================================================================
\* Modification History
\* Created automatically
    """

    cfg_mc_content = f"""
CHECK_DEADLOCK FALSE
\* SPECIFICATION definition
SPECIFICATION
Spec
\* PROPERTY definition
PROPERTY
prop_main
\* Generated automatically
    """

    with open(mc_tla_path, 'w') as mc_tla_file:
        mc_tla_file.write(tla_mc_content)

    with open(mc_cfg_path, 'w') as mc_cfg_file:
        mc_cfg_file.write(cfg_mc_content)

    #print(f"MC.tla and MC.cfg files generated at {mc_tla_path} and {mc_cfg_path}")

#  Парсинг результатов
def parse_tlc_output(output: str):
    results = {}

    # Успешная проверка
    if "Model checking completed. No error has been found." in output:
        results["status"] = "Проверка завершена успешно. Инварианты выполняются."
    elif "Invariant is violated" in output or "Temporal property is violated" in output:
        results["status"] = "!!! Инвариант нарушен!"
    else:
        results["status"] = "!!! Неизвестный результат TLC."

    # Кол-во состояний
    states_match = re.search(r"(\d+) states generated, (\d+) distinct states found", output)
    if states_match:
        results["states_total"] = int(states_match.group(1))
        results["states_distinct"] = int(states_match.group(2))

    # Глубина
    depth_match = re.search(r"The depth of the complete state graph search is (\d+)", output)
    if depth_match:
        results["depth"] = int(depth_match.group(1))

    # Время выполнения
    time_match = re.search(r"Finished in ([\d]+s)", output)
    if time_match:
        results["time"] = time_match.group(1)

    return results


# Запуск верификации
def run_tlc_verification():
    try:
        system = platform.system()
        tla_jar = os.path.join("toolbox_", "tla2tools.jar")
        tla_file = os.path.join("Model", "MC.tla")
        cfg_file = os.path.join("Model", "MC.cfg")

        if not os.path.exists(tla_jar):
            print(f"!!! Не найден файл {tla_jar}. Убедись, что TLA2tools.jar лежит в toolbox_.")
            return

        # Команда запуска TLC
        cmd = ["java", "-jar", tla_jar, "-config", cfg_file, tla_file]

        if system == "Linux":
            cmd.insert(0, "-S")
            cmd.insert(0, "sudo")

            # Ввод пароля один раз
            sudo_pass = getpass.getpass("Введите пароль sudo: ")

            result = subprocess.run(
                cmd,
                input=sudo_pass + "\n",
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True
            )
        else:
            result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True
            )

        output = result.stdout
        with open("Model/tlc_output.log", "w", encoding="utf-8") as f:
            f.write(output)

        parsed = parse_tlc_output(output)

        print(f"\n{parsed.get('status')}")
        print("--- Статистика TLC ---")
        if "states_total" in parsed:
            print(f"- Всего состояний: {parsed['states_total']}")
            print(f"- Уникальных состояний: {parsed['states_distinct']}")
        if "depth" in parsed:
            print(f"- Глубина графа: {parsed['depth']}")
        if "time" in parsed:
            print(f"- Время проверки: {parsed['time']}")

    except Exception as e:
        print(f"!! Ошибка при запуске TLC: {e}")

# Пример запуска
if __name__ == "__main__":
    generate_tla_spec("graph.json", "invariants_kripke.json")
    generate_mc_files("Model/MC.tla", "Model/MC.cfg")
    run_tlc_verification()
