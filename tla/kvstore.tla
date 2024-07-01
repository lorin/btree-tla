(*

# Operations

* get
* insert
* update
* delete

## get
Return NIL if the key is not in the store

## insert 
Return "ok" on success
Return "error" if the key already exists

## update
Return "ok" on success
Return "error" if the key does not exist

## delete

Always returns "ok" 

*)
---- MODULE kvstore ----
EXTENDS TLC


Ops == {"get", "insert", "delete", "update"}
MISSING == CHOOSE x : x \notin Vals
NIL == CHOOSE x : x \notin Vals \union Ops \union {MISSING}

VARIABLES op,
    args,
    ret,
    state, 
    dict, \* tracks mapping of keys to values
    keys \* keys previously inserted


TypeOK ==
    /\ args \in {<<k>>: k \in Keys} \union {<<k,v>>: k \in Keys, v \in Vals} \union {NIL}
    /\ dict \in [Keys -> Vals \union {MISSING}]
    /\ keys \in SUBSET Keys
    /\ op \in Ops \union {NIL} \* initial state for Ops is NIL
    /\ ret \in Vals \union {"ok", "error", MISSING, NIL}
    /\ state \in {"ready", "working"}

Init ==
    /\ op = NIL
    /\ args = NIL
    /\ ret = NIL
    /\ dict = [k \in Keys |-> MISSING]
    /\ state = "ready"
    /\ keys = {}

GetReq(key) == 
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED <<dict, keys>>

GetResp == LET key == args[1] IN 
    /\ op = "get"
    /\ ret' = dict[key]
    /\ state' = "ready"
    /\ UNCHANGED <<op, args, dict, keys>>

InsertReq(key, val) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<key, val>> 
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED <<dict, keys>>

Present(key) == dict[key] \in Vals
Absent(key) == dict[key] = MISSING

InsertResp == LET key == args[1]
                  val == args[2] IN 
       /\ op = "insert"
       /\ dict' = IF Absent(key)
                  THEN [dict EXCEPT ![key] = val] 
                  ELSE dict
       /\ ret' = IF Absent(key) THEN "ok" ELSE "error"
       /\ keys' = keys \union {key}
       /\ state' = "ready"
       /\ UNCHANGED <<op, args>>

UpdateReq(key, val) ==
    /\ op = NIL
    /\ op' = "update"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED <<dict, keys>>

UpdateResp ==
    LET key == args[1]
        val == args[2]
    IN /\ op = "update"
       /\ ret' = IF Present(key) THEN "ok" ELSE "error"
       /\ dict' = IF Present(key)
                  THEN [dict EXCEPT ![key]=val]
                  ELSE dict
       /\ state' = "ready"
       /\ UNCHANGED <<op, args, keys>>
    
DeleteReq(key) ==
    /\ state = "ready"
    /\ op' = "delete"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ state' = "working"
    /\ UNCHANGED <<dict, keys>>

\* we permit deleting keys that aren't there
DeleteResp ==
    LET key == args[1]
    IN /\ op = "delete"
       /\ ret' = "ok"
       /\ state' = "ready"
       /\ keys' = keys \ {key}
       /\ dict' = [dict EXCEPT ![key]=MISSING]
       /\ UNCHANGED <<op, args>>

Next == \/ \E k \in Keys: GetReq(k)
        \/ GetResp
        \/ \E k \in Keys: \E v \in Vals: InsertReq(k, v)
        \/ InsertResp
        \/ \E k \in Keys: \E v \in Vals: UpdateReq(k, v)
        \/ UpdateResp
        \/ \E k \in Keys: DeleteReq(k)
        \/ DeleteResp

vars == <<op, args, ret, dict, keys>>

Spec == Init /\ [Next]_vars

\*
\* invariants
\*

Returned(f) == /\ op = f
               /\ ret # NIL


KeyWrittenMeansNotMissingOnGet ==
    LET key == args[1] IN 
        (Returned("get") /\ key \in keys) => (ret # MISSING)

UpdateSucceedsWhenKeyPresent ==
    LET key == args[1] 
        val == args[2] IN
        (Returned("update") /\ key \in keys) => /\ ret = "ok"
                                                /\ dict[key] = val

UpdateFailsWhenKeyAbsent ==
    LET key == args[1] IN
        (Returned("update") /\ key \in keys) => ret = "error"

InsertSucceeds ==
    LET key == args[1] 
        val == args[2] IN
        (Returned("insert") /\ ret = "ok") => dict[key] = val

InsertFailsMeansKeyAlreadyPresent ==
    LET key == args[1] IN
        (Returned("insert") /\ ret = "error") => dict[key] # MISSING


DeleteSucceeds ==
    LET key == args[1] IN 
    Returned("delete") => dict[key] = MISSING

====