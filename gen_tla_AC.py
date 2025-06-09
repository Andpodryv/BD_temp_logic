import json
import os
import subprocess
import time
import platform
from pathlib import Path
from tabulate import tabulate
import webbrowser
import re

# Константы
TLA_DIR = Path("Model_AC")
TLA_DIR.mkdir(exist_ok=True)
TLA_JAR = os.path.join("toolbox_", "tla2tools.jar")
MODULE_CFG = "MC"
ENCODING = "utf-8"

# Открытие графа и пользователей
with open("graph.json", encoding=ENCODING) as f:
    graph = json.load(f)
with open("users.json", encoding=ENCODING) as f:
    users = json.load(f)
with open("roles_config.json", encoding=ENCODING) as f:
    role_config = json.load(f)

# Парсинг конфиг файла ролей
ROLES = role_config["Roles"]
DEPARTMENTS = role_config["Departments"]
TIMETYPE = role_config["TimeType"]
ROLE_INITS = role_config["RoleInitializations"]
ACCESS_CONTEXT = role_config.get("AccessContext", {})
CURRENT_TIME = ACCESS_CONTEXT.get("CurrentTime", "Working")

# Парсинг PropertyMap, Edges, States
def parse_graph(graph_data):
    prop_map, edges, states = [], set(), []
    for node in graph_data["nodes"]:
        sid = f"S{node['id']}"
        states.append(sid)
        props = ", ".join(f'"{p}"' for p in node["properties"])
        prop_map.append(f"{sid} |-> {{{props}}}")
        for target in node["outgoing_edges"]:
            edges.add(f'<<"{sid}", "S{target}">>')
    return states, sorted(edges), prop_map

states, edges, propmap = parse_graph(graph)

# Блоки для всех спецификаций из распарсенного конфига
def generate_role_defs():
    roles = ", ".join(f'"{r}"' for r in ROLES)
    deps = ", ".join(f'"{d}"' for d in DEPARTMENTS)
    time = ", ".join(f'"{t}"' for t in TIMETYPE)
    return f'''
Roles == {{{roles}}}
Departments == {{{deps}}}
TimeType == {{{time}}}
ScheduleType == [ Time: TimeType ]

RoleType == [ department : Departments, role_name : Roles, schedule : ScheduleType ]
UserType == [ name : STRING, role : RoleType ]
'''

def generate_role_init_defs():
    lines = []
    for name, data in ROLE_INITS.items():
        sched_set = ", ".join(f'[Time |-> "{s}"]' for s in data["schedule"])
        lines.append(f'{name} == [department |-> "{data["department"]}", role_name |-> "{data["role_name"]}", schedule |-> {{{sched_set}}}]')
    return "\n".join(lines)

def generate_access_logic(access_rules):
    lines = []

    lines.append("DepartmentMatch(dept, props) ==\n  \\E p \\in props :")
    dm_cases = []
    for dept, info in access_rules.items():
        for dtype in info["types"]:
            dm_cases.append(f'(dept = "{dept}" /\\ p = "{dtype}")')
    lines.append("    \\/ " + "\n    \\/ ".join(dm_cases))
    lines.append("")

    # Генерация StageAllowed
    for dept, info in access_rules.items():
        for role, allowed in info["roles"].items():
            if allowed == "ALL":
                continue  # ALL — доступен к любым стадиям
            fname = f"Stage_{dept}_{role}".replace("-", "_")
            stages = "{" + ", ".join(f'"{s}"' for s in allowed) + "}"
            lines.append(f"{fname}(props) ==")
            lines.append(f"  \\E p \\in props : p \\in {stages}\n")

    # Генерация главной функции CanAccess
    lines.append("CanAccess(user, s, curtime) ==\n  LET props == PropertyMap[s] IN")
    ca_lines = []
    ca_lines.append(
        '    \\/ (user.role.role_name = "Admin" /\\ DepartmentMatch(user.role.department, props))'
    )

    for dept, info in access_rules.items():
        for role, allowed in info["roles"].items():
            condition = f'user.role.department = "{dept}" /\\ user.role.role_name = "{role}" /\\ DepartmentMatch("{dept}", props)'
            if allowed != "ALL":
                fname = f"Stage_{dept}_{role}".replace("-", "_")
                condition += f" /\\ {fname}(props)"
            condition += " /\\ curtime \\in user.role.schedule"
            ca_lines.append(f"    \\/ ({condition})")

    lines.append("\n".join(ca_lines))
    return "\n".join(lines)


access_logic = generate_access_logic(role_config["AccessRules"])
access_logic += '''
RequestAccess(user, s) ==
  /\ AccessMap' = [AccessMap EXCEPT ![user.name] = @ \cup {s}]
  /\ AllAccessedStates' = AllAccessedStates \cup {s}
  /\ PrintT("States: " \o ToString(AllAccessedStates))
  /\ UNCHANGED <<U, R>> '''

access_logic += f'''
RequestAccessD ==
  \E u \in U :
    \E s \in States :
       CanAccess(u, s, [Time |-> "{CURRENT_TIME}"]) /\ ~(s \in AccessMap[u.name]) /\ RequestAccess(u, s)'''

access_logic += '''
Next == RequestAccessD

TemporalAssumption == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ TemporalAssumption

Inv_AccessConsistency ==
  \A u \in U : \A s \in AccessMap[u.name] : \E t \in ScheduleType : CanAccess(u, s, t)

Inv_OnlyValidStates ==
  \A name \in DOMAIN AccessMap : AccessMap[name] \subseteq States

Inv_NoDuplicateAccess ==
  \A u \in U : AccessMap[u.name] = UNION { {s} : s \in AccessMap[u.name] }

Inv_AdminPower ==
  \A u \in U : u.role.role_name = "Admin" => \A s \in AccessMap[u.name] : DepartmentMatch(u.role.department, PropertyMap[s])

EventuallySomeAccess ==
  <> (\E name \in DOMAIN AccessMap : AccessMap[name] # {})

Invariants == Inv_AccessConsistency /\ Inv_OnlyValidStates /\ Inv_NoDuplicateAccess /\ Inv_AdminPower /\ EventuallySomeAccess
'''

# Генерация спецификации для пользователя
def generate_user_spec(user, states, edges, propmap):
    username = user["name"]
    role = user["role"]
    ac_file = TLA_DIR / f"AC_{username}.tla"

    states_str = "States == {" + ", ".join(f'"{s}"' for s in states) + "}"
    edges_str = "Edges == {\n  " + ",\n  ".join(edges) + "\n}"
    propmap_str = "PropertyMap == [\n  " + ",\n  ".join(propmap) + "\n]"

    init_roles = ", ".join(ROLE_INITS.keys())

    init_block = f'''
Init ==
  /\ R = {{{init_roles}}}
  /\ U = {{
      [ name |-> "{username}", role |-> {role} ] }}
  /\ AllAccessedStates = {{}}
  /\ AccessMap = [u \in {{u.name : u \in U}} |-> {{}}]
'''

    content = f'''------------------------------ MODULE AC_{username} ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLES U, R, AccessMap, AllAccessedStates
vars == << U, R, AccessMap, AllAccessedStates >>

{states_str}
{edges_str}
{propmap_str}

{generate_role_defs()}
{generate_role_init_defs()}
{init_block}
{access_logic}
=============================================================================
\\* Generated on {time.ctime()} by stand.py
'''
    ac_file.write_text(content, encoding=ENCODING)

# Генерация конфиг. файлов
def generate_mc_files(username):
    prop_id = f"prop_{int(time.time_ns())}"
    mc_tla = TLA_DIR / f"{MODULE_CFG}.tla"
    mc_cfg = TLA_DIR / f"{MODULE_CFG}.cfg"

    mc_tla.write_text(f"""---- MODULE {MODULE_CFG} ----
EXTENDS AC_{username}, TLC

(* PROPERTY definition @modelCorrectnessProperties:0 *)
{prop_id} ==
[]Invariants

=============================================================================
\\* Created {time.ctime()} by stand.py
""", encoding=ENCODING)

    mc_cfg.write_text(f"""CHECK_DEADLOCK FALSE
\\* SPECIFICATION definition
SPECIFICATION
Spec

\\* PROPERTY definition
PROPERTY
{prop_id}

\\* Generated on {time.ctime()}
""", encoding=ENCODING)

# Запуск верификации спецификации
def run_tlc_verification(username, sudo_pass=None):
    try:
        system = platform.system()
        tla_file = os.path.join("Model_AC", "MC.tla")
        cfg_file = os.path.join("Model_AC", "MC.cfg")
        log_file = TLA_DIR / f"{username}_states.log"

        if not os.path.exists(TLA_JAR):
            print(f"!!! Не найден файл {TLA_JAR}. Убедись, что TLA2tools.jar лежит в toolbox_.")
            return

        cmd = ["java", "-jar", TLA_JAR,"-config", cfg_file, tla_file, "-userFile", log_file]

        if system == "Linux":
            cmd.insert(0, "-S")
            cmd.insert(0, "sudo")
            if sudo_pass is None:
                import getpass
                sudo_pass = getpass.getpass(" Введите пароль sudo: ")
            result = subprocess.run(cmd, input=sudo_pass + "\n", stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        else:
            result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)

        output = result.stdout
        log_file = TLA_DIR / f"{username}_tlc.log"
        log_file.write_text(output, encoding=ENCODING)

    except Exception as e:
        print(f"!!! Ошибка при запуске TLC: {e}")

# Парсинг логов,
def parse_access_log(username):

    log_path = TLA_DIR / f"{username}_states.log"
    if not log_path.exists():
        return []

    all_states = set()

    with log_path.open(encoding=ENCODING) as f:
        for line in f:
            if "States:" in line:
                match = re.search(r'States:\s*\{(.*?)\}', line)
                if match:
                    states_raw = match.group(1)
                    states = re.findall(r'S\d+', states_raw)
                    all_states.update(states)

    return sorted(all_states, key=lambda s: int(s[1:]))


# Отрисовка матрицы доступа
def save_access_matrix_html(matrix, html_path):
    all_states = sorted({s for states in matrix.values() for s in states}, key=lambda x: int(x[1:]))
    headers = ["User"] + all_states
    rows = []
    for user, accessed in matrix.items():
        row = [user] + [("✔" if s in accessed else "✘") for s in all_states]
        rows.append(row)

    html = """
    <html>
    <head>
        <meta charset="utf-8">
        <title>Access Matrix</title>
        <style>
            body { font-family: Arial, sans-serif; padding: 20px; }
            table { border-collapse: collapse; width: 100%; }
            th, td { border: 1px solid #999; padding: 8px; text-align: center; }
            th { background-color: #f2f2f2; }
            td:first-child, th:first-child { text-align: left; }
            .✔ { background-color: #6edc5f; }
            .✘ { background-color: #ff4c4c; }
        </style>
    </head>
    <body>
        <h2>Access Matrix</h2>
        <table>
            <tr>""" + "".join(f"<th>{h}</th>" for h in headers) + "</tr>"

    for row in rows:
        html += "<tr>" + "".join(f"<td class='{cell}'>{cell}</td>" for cell in row) + "</tr>"
    html += """
        </table>
    </body>
    </html>
    """

    path = Path(html_path)
    path.write_text(html, encoding="utf-8")
    webbrowser.open(path.absolute().as_uri())

def parse_output(username):
    log_path = TLA_DIR / f"{username}_tlc.log"
    if not log_path.exists():
        print(f"Лог-файл {log_path} не найден для пользователя {username}")
        return False

    with log_path.open(encoding=ENCODING) as f:
        content = f.read()

    success_msg = "Model checking completed. No error has been found."

    if success_msg in content:
        print(f"Верификация успешна для пользователя {username}")
        return True
    else:
        print(f"Ошибка верификации для пользователя {username}")
        return False

def print_summary(elapsed, all_ok):
    print("\n Общая длительность верификации: {:.2f} секунд".format(elapsed))

    if all_ok:
        print(" Все спецификации успешно прошли верификацию!")
    else:
        print("Некоторые спецификации завершились с ошибками.")

# main функция
def AC_verif():
    access_matrix = {}
    sudo_pass = None
    if platform.system() == "Linux":
        import getpass
        sudo_pass = getpass.getpass("Введите пароль sudo один раз: ")

    all_ok = True
    start_time = time.time()  # ⏱ старт таймера

    for user in users:
        username = user["name"]
        generate_user_spec(user, states, edges, propmap)
        generate_mc_files(username)
        run_tlc_verification(username, sudo_pass=sudo_pass)

        if not parse_output(username):
            all_ok = False

        access_matrix[username] = parse_access_log(username)

    elapsed = time.time() - start_time  # ⏱ конец таймера
    print_summary(elapsed, all_ok)

    save_access_matrix_html(access_matrix, "access_matrix.html")


if __name__ == "__main__":
    AC_verif()
