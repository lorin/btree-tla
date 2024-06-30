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

CONSTANTS Keys, Vals

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
    /\ op \in Ops
    /\ args \in {<<k>>: k \in Keys} \union {<<k,v>>: k \in Keys, v \in Vals}
    /\ ret \in Vals \union {"ok", "error", MISSING, NIL}
    /\ state \in {"ready", "working"}
    /\ dict \in [Keys -> Vals \union {MISSING}]
    /\ keys \in Keys

Init ==
    /\ op = NIL
    /\ args = << >>
    /\ ret = NIL
    /\ dict = [k \in Keys |-> MISSING]
    /\ keys = {}

GetReq(key) == 
    /\ op = NIL
    /\ op' = "get"
    /\ args' = <<key>>
    /\ ret' = NIL
    /\ UNCHANGED <<ret, dict, keys>>

GetResp ==
    /\ op = "get"
    /\ op' = NIL
    /\ args' = <<>>
    /\ LET key == args[1] 
        IN ret' = dict[key]
    /\ UNCHANGED <<dict, keys>>

InsertReq(key, val) ==
    /\ op = NIL
    /\ op' = "insert"
    /\ args' = <<key, val>> 
    /\ ret' = NIL
    /\ UNCHANGED <<dict, keys>>

InsertResp == 
    LET key == args[1]
        val == args[2] 
    IN /\ op = "insert"
       /\ dict' = IF dict[key] = NIL 
                  THEN [dict EXCEPT ![key] = val] 
                  ELSE dict
       /\ ret' = IF dict[key] = NIL THEN "ok" ELSE "error"
       /\ op' = NIL
       /\ args' = <<>>
       /\ keys' = keys \union {key}

UpdateReq(key, val) ==
    /\ op = NIL
    /\ op' = "update"
    /\ args' = <<key, val>>
    /\ ret' = NIL
    /\ UNCHANGED <<dict, keys>>

UpdateResp ==
    LET key == args[1]
        val == args[2]
    IN /\ op = "update"
       /\ dict' = IF dict[key] # NIL
                  THEN [dict EXCEPT ![key]=val]
                  ELSE dict
       /\ ret' = IF dict[key] # NIL THEN "ok" ELSE "error"
       /\ op' = NIL
       /\ args' = <<>>
       /\ UNCHANGED keys
    
DeleteReq(key) ==
    /\ op = NIL
    /\ op' = "delete"
    /\ args = <<key>>
    /\ ret' = NIL
    /\ UNCHANGED <<dict, keys>>

DeleteResp ==
    LET key == args[1]
    IN /\ op = "delete"
       /\ dict' = [dict EXCEPT ![key]=NIL]
       /\ op' = NIL
       /\ args' = <<>>
       /\ keys' = keys \ {key}

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

====