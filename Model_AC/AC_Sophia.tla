------------------------------ MODULE AC_Sophia ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

VARIABLES U, R, AccessMap, AllAccessedStates
vars == << U, R, AccessMap, AllAccessedStates >>

States == {"S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S9", "S10", "S11", "S12", "S13", "S14", "S15", "S16", "S17", "S18", "S19", "S20", "S21", "S22", "S23", "S24", "S25"}
Edges == {
  <<"S0", "S1">>,
  <<"S1", "S2">>,
  <<"S10", "S11">>,
  <<"S11", "S12">>,
  <<"S11", "S20">>,
  <<"S12", "S19">>,
  <<"S13", "S14">>,
  <<"S14", "S15">>,
  <<"S15", "S21">>,
  <<"S19", "S11">>,
  <<"S2", "S10">>,
  <<"S2", "S13">>,
  <<"S2", "S3">>,
  <<"S2", "S7">>,
  <<"S24", "S25">>,
  <<"S25", "S24">>,
  <<"S3", "S4">>,
  <<"S4", "S5">>,
  <<"S5", "S5">>,
  <<"S5", "S6">>,
  <<"S6", "S16">>,
  <<"S6", "S17">>,
  <<"S6", "S18">>,
  <<"S7", "S8">>,
  <<"S8", "S7">>,
  <<"S8", "S9">>,
  <<"S9", "S22">>,
  <<"S9", "S23">>,
  <<"S9", "S24">>
}
PropertyMap == [
  S0 |-> {"source=raw", "received"},
  S1 |-> {"source=raw", "normalized"},
  S2 |-> {"source=raw", "filtered"},
  S3 |-> {"type=scada", "tags_extracted"},
  S4 |-> {"type=scada", "validated"},
  S5 |-> {"type=scada", "aggregated"},
  S6 |-> {"type=scada", "stored", "db=cassandra"},
  S7 |-> {"type=pii", "anonymized"},
  S8 |-> {"type=pii", "checked"},
  S9 |-> {"type=pii", "stored", "db=mongodb"},
  S10 |-> {"type=log", "logs_parsed"},
  S11 |-> {"type=log", "analyzed"},
  S12 |-> {"type=log", "stored", "db=mongodb"},
  S13 |-> {"type=image", "compressed"},
  S14 |-> {"type=image", "ai_marked"},
  S15 |-> {"type=image", "stored", "db=cassandra"},
  S16 |-> {"type=scada", "archived", "storage=hdfs"},
  S17 |-> {"type=scada", "reported", "target=office"},
  S18 |-> {"type=scada", "visualized", "target=plant"},
  S19 |-> {"type=log", "reported", "target=office"},
  S20 |-> {"type=log", "archived", "db=mongodb"},
  S21 |-> {"type=image", "archived", "storage=glacier"},
  S22 |-> {"type=pii", "exported", "target=legal"},
  S23 |-> {"type=pii", "access_granted", "target=users"},
  S24 |-> {"type=pii", "archived", "db=postgresql"},
  S25 |-> {"type=pii", "expired_deleted"}
]


Roles == {"Admin", "ShiftA", "ShiftB", "ShiftC", "Analyst", "NightAnalyst", "Senior", "Junior", "ImageWorker", "SupportWorker"}
Departments == {"SCADA", "SOC", "PII", "IMG", "SUPPORT"}
TimeType == {"Working", "NonWorking"}
ScheduleType == [ Time: TimeType ]

RoleType == [ department : Departments, role_name : Roles, schedule : ScheduleType ]
UserType == [ name : STRING, role : RoleType ]

SCADA_Admin == [department |-> "SCADA", role_name |-> "Admin", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
SCADA_ShiftA == [department |-> "SCADA", role_name |-> "ShiftA", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
SCADA_ShiftB == [department |-> "SCADA", role_name |-> "ShiftB", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
SCADA_ShiftC == [department |-> "SCADA", role_name |-> "ShiftC", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
SOC_Admin == [department |-> "SOC", role_name |-> "Admin", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
SOC_Analyst == [department |-> "SOC", role_name |-> "Analyst", schedule |-> {[Time |-> "Working"]}]
SOC_NightAnalyst == [department |-> "SOC", role_name |-> "NightAnalyst", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
PII_Admin == [department |-> "PII", role_name |-> "Admin", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
PII_Senior == [department |-> "PII", role_name |-> "Senior", schedule |-> {[Time |-> "Working"]}]
PII_Junior == [department |-> "PII", role_name |-> "Junior", schedule |-> {[Time |-> "Working"]}]
IMG_Admin == [department |-> "IMG", role_name |-> "Admin", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
IMG_Worker == [department |-> "IMG", role_name |-> "ImageWorker", schedule |-> {[Time |-> "Working"]}]
Support_Admin == [department |-> "SUPPORT", role_name |-> "Admin", schedule |-> {[Time |-> "Working"], [Time |-> "NonWorking"]}]
Support_Worker == [department |-> "SUPPORT", role_name |-> "SupportWorker", schedule |-> {[Time |-> "Working"]}]

Init ==
  /\ R = {SCADA_Admin, SCADA_ShiftA, SCADA_ShiftB, SCADA_ShiftC, SOC_Admin, SOC_Analyst, SOC_NightAnalyst, PII_Admin, PII_Senior, PII_Junior, IMG_Admin, IMG_Worker, Support_Admin, Support_Worker}
  /\ U = {
      [ name |-> "Sophia", role |-> PII_Senior ] }
  /\ AllAccessedStates = {}
  /\ AccessMap = [u \in {u.name : u \in U} |-> {}]


DepartmentMatch(dept, props) ==
  \E p \in props :
    \/ (dept = "SCADA" /\ p \in {"type=scada"})
    \/ (dept = "SOC" /\ p \in {"type=log"})
    \/ (dept = "PII" /\ p \in {"type=pii"})
    \/ (dept = "IMG" /\ p \in {"type=image"})
    \/ (dept = "SUPPORT" /\ p \in {"source=raw"})

StageAllowedForSCADA(props) ==
  \E p \in props : p \in {"aggregated", "stored", "archived", "visualized", "reported"}

RoleAllowedForPII(user, props) ==
  \/ (user.role.role_name = "Senior")
  \/ (user.role.role_name = "Junior"
      /\ \E p \in props : p \in {"expired_deleted", "archived", "access_granted", "exported"})

StageAllowedForSupport(props) ==
  \E p \in props : p \in {"source=raw", "anonymized", "filtered"}

CanAccess(user, s, curtime) ==
  LET props == PropertyMap[s] IN
    \/ (user.role.role_name = "Admin" /\ DepartmentMatch(user.role.department, props))
    \/ (user.role.department = "SCADA" /\ user.role.role_name \in {"ShiftA", "ShiftB", "ShiftC"} /\ DepartmentMatch("SCADA", props) /\ StageAllowedForSCADA(props) /\ curtime \in user.role.schedule)
    \/ (user.role.department = "SOC" /\ user.role.role_name \in {"Analyst", "NightAnalyst"} /\ DepartmentMatch("SOC", props) /\ curtime \in user.role.schedule)
    \/ (user.role.department = "PII" /\ DepartmentMatch("PII", props) /\ RoleAllowedForPII(user, props) /\ curtime \in user.role.schedule)
    \/ (user.role.department = "IMG" /\ user.role.role_name = "ImageWorker" /\ DepartmentMatch("IMG", props) /\ curtime \in user.role.schedule)
    \/ (user.role.department = "SUPPORT" /\ user.role.role_name = "SupportWorker" /\ DepartmentMatch("SUPPORT", props) /\ StageAllowedForSupport(props) /\ curtime \in user.role.schedule)

RequestAccess(user, s) ==
  /\ AccessMap' = [AccessMap EXCEPT ![user.name] = @ \cup {s}]
  /\ AllAccessedStates' = AllAccessedStates \cup {s}
  /\ PrintT("States: " \o ToString(AllAccessedStates))
  /\ UNCHANGED <<U, R>>

RequestAccessD ==
  \E u \in U :
    \E s \in States :
      CanAccess(u, s, [Time |-> "Working"]) /\ ~(s \in AccessMap[u.name]) /\ RequestAccess(u, s)


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

=============================================================================
\* Generated on Fri May 23 03:58:54 2025 by stand.py
