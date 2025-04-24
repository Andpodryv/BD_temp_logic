import json
import subprocess
import os

def print_invariants():
    invariants = [
        "1. Если SCADA-данные были визуализированы, то до этого они были агрегированы и валидированы.",
        "2. Если SCADA-данные были архивированы, они должны были быть сохранены.",
        "3. Если PII был экспортирован или предоставлен доступ, то до этого он был анонимизирован и проверен.",
        "4. Если SCADA сохранены, значит были агрегированы.",
        "5. Если PII проверены, то до этого они были анонимизированы.",
        "6. Если лог был архивирован или отправлен, значит ранее он был проанализирован.",
        "7. Если изображение сохранено или архивировано, значит было размечено AI.",
        "8. Если PII удалены по сроку, то они ранее были архивированы.",
    ]
    print("\nПроверяемые инварианты:\n")
    for inv in invariants:
        print(inv)

def generate_tla_spec(graph_path: str, tla_path: str = "main.tla"):
    with open(graph_path, "r", encoding="utf-8") as f:
        data = json.load(f)

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

        f.write("""
IsPII(s) == "type=pii" \in PropertyMap[s]
IsSCADA(s) == "type=scada" \in PropertyMap[s]
IsLog(s) == "type=log" \in PropertyMap[s]
IsImage(s) == "type=image" \in PropertyMap[s]\n""")


        f.write('Init == Trace = << "S0" >>\n')

        f.write("""
        Next ==
          \\E t \\in States :
            /\\ <<Trace[Len(Trace)], t>> \\in Edges
            /\\ ~(\\E i \\in 1..Len(Trace) : Trace[i] = t)
            /\\ Trace' = Trace \\o <<t>>


(* Если SCADA-данные были визуализированы, то до этого они были агрегированы и валидированы *)
Invariant1 ==
  \\A i \\in 1..Len(Trace) :
    ("visualized" \\in PropertyMap[Trace[i]] /\\ IsSCADA(Trace[i])) =>
      (\\E j \\in 1..(i-1) : "aggregated" \\in PropertyMap[Trace[j]] /\\ IsSCADA(Trace[j])) /\\
      (\\E k \\in 1..(i-1) : "validated" \\in PropertyMap[Trace[k]] /\\ IsSCADA(Trace[k]))

(* Если SCADA-данные были архивированы, они должны были быть сохранены *)
Invariant2 ==
  \\A i \\in 1..Len(Trace) :
    ("archived" \\in PropertyMap[Trace[i]] /\\ IsSCADA(Trace[i])) =>
      \\E j \\in 1..(i-1) : "stored" \\in PropertyMap[Trace[j]] /\\ IsSCADA(Trace[j])

(* Если PII был экспортирован или предоставлен доступ, то до этого он был анонимизирован и проверен *)
Invariant3 ==
  \\A i \\in 1..Len(Trace) :
    (("exported" \\in PropertyMap[Trace[i]] \\/ "access_granted" \\in PropertyMap[Trace[i]]) /\\ IsPII(Trace[i])) =>
      (\\E j \\in 1..(i-1) : "anonymized" \\in PropertyMap[Trace[j]] /\\ IsPII(Trace[j])) /\\
      (\\E k \\in 1..(i-1) : "checked" \\in PropertyMap[Trace[k]] /\\ IsPII(Trace[k]))

(* Если SCADA сохранены, значит были агрегированы *)
Invariant4 ==
  \\A i \\in 1..Len(Trace) :
    ("stored" \\in PropertyMap[Trace[i]] /\\ IsSCADA(Trace[i])) =>
      \\E j \\in 1..(i-1) : "aggregated" \\in PropertyMap[Trace[j]] /\\ IsSCADA(Trace[j])

(* Если PII проверены, то до этого они были анонимизированы *)
Invariant5 ==
  \\A i \\in 1..Len(Trace) :
    ("checked" \\in PropertyMap[Trace[i]] /\\ IsPII(Trace[i])) =>
      \\E j \\in 1..(i-1) : "anonymized" \\in PropertyMap[Trace[j]] /\\ IsPII(Trace[j])

(* Если лог был архивирован или отправлен, значит ранее он был проанализирован *)
Invariant6 ==
  \\A i \\in 1..Len(Trace) :
    (("archived" \\in PropertyMap[Trace[i]] \\/ ("reported" \\in PropertyMap[Trace[i]] /\\ "target=it" \\in PropertyMap[Trace[i]])) /\\ IsLog(Trace[i])) =>
      \\E j \\in 1..(i-1) : "analyzed" \\in PropertyMap[Trace[j]] /\\ IsLog(Trace[j])

(* Если изображение сохранено или архивировано, значит было размечено AI *)
Invariant7 ==
  \\A i \\in 1..Len(Trace) :
    ("stored" \\in PropertyMap[Trace[i]] /\\ IsImage(Trace[i])) =>
      \\E j \\in 1..(i-1) : "ai_marked" \\in PropertyMap[Trace[j]] /\\ IsImage(Trace[j])
  /\\
  \\A k \\in 1..Len(Trace) :
    ("archived" \\in PropertyMap[Trace[k]] /\\ "storage=glacier" \\in PropertyMap[Trace[k]] /\\ IsImage(Trace[k])) =>
      \\E m \\in 1..(k-1) : "ai_marked" \\in PropertyMap[Trace[m]] /\\ IsImage(Trace[m])

(* Если PII удалены по сроку, то они ранее были архивированы *)
Invariant8 ==
  \\A i \\in 1..Len(Trace) :
    ("expired_deleted" \\in PropertyMap[Trace[i]] /\\ IsPII(Trace[i])) =>
      \\E j \\in 1..(i-1) : "archived" \\in PropertyMap[Trace[j]] /\\ IsPII(Trace[j])


AllInvariants == /\\ Invariant1
                 /\\ Invariant2
                 /\\ Invariant3
                 /\\ Invariant4
                 /\\ Invariant5
                 /\\ Invariant6
                 /\\ Invariant7
                 /\\ Invariant8

Spec == Init /\\ [][Next]_<<Trace>>

THEOREM Spec => <>[]AllInvariants

==============================================================================
""")

def generate_mc_files(mc_tla_path, mc_cfg_path):
    tla_mc_content = f"""
---- MODULE MC ----
EXTENDS main, TLC

\* PROPERTY definition @modelCorrectnessProperties:0
prop_174472089399451000 ==
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
prop_174472089399451000
\* Generated automatically
    """

    with open(mc_tla_path, 'w') as mc_tla_file:
        mc_tla_file.write(tla_mc_content)

    with open(mc_cfg_path, 'w') as mc_cfg_file:
        mc_cfg_file.write(cfg_mc_content)

    print(f"MC.tla and MC.cfg files generated at {mc_tla_path} and {mc_cfg_path}")


def run_tlc_verification():
    command = ["sudo", "-S", "java", "-jar", "toolbox_/tla2tools.jar", "-config", "Model/MC.cfg",
               "Model/MC.tla"]
    try:
        password = input("Enter sudo password: ")
        process = subprocess.Popen(command, stdin=subprocess.PIPE)
        process.communicate(input=f"{password}\n".encode())
    except Exception as e:
        print(f"Error running TLC: {e}")


# Пример запуска
if __name__ == "__main__":
    generate_tla_spec("graph.json")
    generate_mc_files("Model/MC.tla", "Model/MC.cfg")
    run_tlc_verification()
