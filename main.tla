------------------------------- MODULE main -------------------------------
EXTENDS Sequences, TLC, FiniteSets, Integers

VARIABLES Trace

States == {"S0", "S1", "S2", "S3", "S4", "S5", "S6", "S7", "S8", "S9", "S10", "S11", "S12", "S13", "S14", "S15", "S16", "S17", "S18", "S19", "S20", "S21", "S22", "S23", "S24", "S25"}

Edges == {
  <<"S0", "S1">>, <<"S1", "S2">>, <<"S2", "S3">>, <<"S2", "S7">>, <<"S2", "S10">>, <<"S2", "S13">>, <<"S3", "S4">>, <<"S4", "S5">>, <<"S5", "S5">>, <<"S5", "S6">>, <<"S6", "S16">>, <<"S6", "S18">>, <<"S6", "S17">>, <<"S7", "S8">>, <<"S8", "S7">>, <<"S8", "S9">>, <<"S9", "S22">>, <<"S9", "S23">>, <<"S9", "S24">>, <<"S10", "S11">>, <<"S11", "S20">>, <<"S11", "S12">>, <<"S12", "S19">>, <<"S13", "S14">>, <<"S14", "S15">>, <<"S15", "S21">>, <<"S19", "S11">>, <<"S24", "S25">>, <<"S25", "S24">>
}

PropertyMap == [
  S0 |-> {"received", "source=raw"},
  S1 |-> {"normalized", "source=raw"},
  S2 |-> {"filtered", "source=raw"},
  S3 |-> {"tags_extracted", "type=scada"},
  S4 |-> {"type=scada", "validated"},
  S5 |-> {"aggregated", "type=scada"},
  S6 |-> {"db=cassandra", "stored", "type=scada"},
  S7 |-> {"anonymized", "type=pii"},
  S8 |-> {"checked", "type=pii"},
  S9 |-> {"db=mongodb", "stored", "type=pii"},
  S10 |-> {"logs_parsed", "type=log"},
  S11 |-> {"analyzed", "type=log"},
  S12 |-> {"db=mongodb", "stored", "type=log"},
  S13 |-> {"compressed", "type=image"},
  S14 |-> {"ai_marked", "type=image"},
  S15 |-> {"db=cassandra", "stored", "type=image"},
  S16 |-> {"archived", "storage=hdfs", "type=scada"},
  S17 |-> {"reported", "target=office", "type=scada"},
  S18 |-> {"target=plant", "type=scada", "visualized"},
  S19 |-> {"reported", "target=office", "type=log"},
  S20 |-> {"archived", "db=mongodb", "type=log"},
  S21 |-> {"archived", "storage=glacier", "type=image"},
  S22 |-> {"exported", "target=legal", "type=pii"},
  S23 |-> {"access_granted", "target=users", "type=pii"},
  S24 |-> {"archived", "db=postgresql", "type=pii"},
  S25 |-> {"expired_deleted", "type=pii"}
]

IsImage(s) == "type=image" \in PropertyMap[s]
IsLog(s) == "type=log" \in PropertyMap[s]
IsPii(s) == "type=pii" \in PropertyMap[s]
IsScada(s) == "type=scada" \in PropertyMap[s]
Init == Trace = << "S0" >>

        Next ==
          \E t \in States :
            /\ <<Trace[Len(Trace)], t>> \in Edges
            /\ ~(\E i \in 1..Len(Trace) : Trace[i] = t)
            /\ Trace' = Trace \o <<t>>

(* Если SCADA-данные были визуализированы, то до этого они были агрегированы и валидированы *)
Invariant1 ==
  \A i \in 1..Len(Trace) :
    ("visualized" \in PropertyMap[Trace[i]] /\ IsScada(Trace[i])) =>
      \E j1 \in 1..(i-1) : "validated" \in PropertyMap[Trace[j1]] /\ IsScada(Trace[j1]) /\
      \E j2 \in 1..(i-1) : "aggregated" \in PropertyMap[Trace[j2]] /\ IsScada(Trace[j2])

(* Если SCADA-данные были архивированы, они должны были быть сохранены *)
Invariant2 ==
  \A i \in 1..Len(Trace) :
    ("archived" \in PropertyMap[Trace[i]] /\ IsScada(Trace[i])) =>
      \E j1 \in 1..(i-1) : "stored" \in PropertyMap[Trace[j1]] /\ IsScada(Trace[j1])

(* Если PII был экспортирован или предоставлен доступ, то до этого он был анонимизирован и проверен *)
Invariant3 ==
  \A i \in 1..Len(Trace) :
    ("exported" \in PropertyMap[Trace[i]] /\ IsPii(Trace[i])) =>
      \E j1 \in 1..(i-1) : "anonymized" \in PropertyMap[Trace[j1]] /\ IsPii(Trace[j1]) /\
      \E j2 \in 1..(i-1) : "checked" \in PropertyMap[Trace[j2]] /\ IsPii(Trace[j2])

(* Если SCADA-данные были сохранены, значит они были агрегированы *)
Invariant4 ==
  \A i \in 1..Len(Trace) :
    ("stored" \in PropertyMap[Trace[i]] /\ IsScada(Trace[i])) =>
      \E j1 \in 1..(i-1) : "aggregated" \in PropertyMap[Trace[j1]] /\ IsScada(Trace[j1])

(* Если PII были проверены, то до этого они были анонимизированы *)
Invariant5 ==
  \A i \in 1..Len(Trace) :
    ("checked" \in PropertyMap[Trace[i]] /\ IsPii(Trace[i])) =>
      \E j1 \in 1..(i-1) : "anonymized" \in PropertyMap[Trace[j1]] /\ IsPii(Trace[j1])

(* Если лог был архивирован или отправлен, значит ранее он был проанализирован *)
Invariant6 ==
  \A i \in 1..Len(Trace) :
    ("archived" \in PropertyMap[Trace[i]] /\ IsLog(Trace[i])) =>
      \E j1 \in 1..(i-1) : "analyzed" \in PropertyMap[Trace[j1]] /\ IsLog(Trace[j1])

(* Если изображение сохранено или архивировано, значит оно было размечено AI *)
Invariant7 ==
  \A i \in 1..Len(Trace) :
    ("stored" \in PropertyMap[Trace[i]] /\ IsImage(Trace[i])) =>
      \E j1 \in 1..(i-1) : "ai_marked" \in PropertyMap[Trace[j1]] /\ IsImage(Trace[j1])

(* Если PII удалены по сроку, то они ранее были архивированы *)
Invariant8 ==
  \A i \in 1..Len(Trace) :
    ("expired_deleted" \in PropertyMap[Trace[i]] /\ IsPii(Trace[i])) =>
      \E j1 \in 1..(i-1) : "archived" \in PropertyMap[Trace[j1]] /\ IsPii(Trace[j1])

AllInvariants == Invariant1 /\ Invariant2 /\ Invariant3 /\ Invariant4 /\ Invariant5 /\ Invariant6 /\ Invariant7 /\ Invariant8




Spec == Init /\ [][Next]_<<Trace>>

THEOREM Spec => <>[]AllInvariants

==============================================================================
