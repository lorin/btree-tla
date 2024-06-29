(*

Operations:
    get
    insert
    update
    delete

insert: 
    - will return an error if the key already exists
*)
---- MODULE kvstore ----
EXTENDS TLC

CONSTANTS Keys, Values

NULL == CHOOSE x : x \notin (Values \union {"insert"})

VARIABLES op,
    args,
    ret,
    dict \* tracks mapping of keys to values

Init ==
    /\ op = NULL
    /\ args = << >>
    /\ ret = NULL
    /\ dict = [k \in Keys |-> NULL]

InsertReq(key, val) ==
    /\ op = NULL
    /\ op' = "insert"
    /\ args' = <<key, val>> 
    /\ UNCHANGED <<ret, dict>>

InsertResp == 
    LET key == args[1]
        val == args[2] 
    IN /\ op = "insert"
       /\ dict' = IF dict[key] = NULL 
                  THEN [dict EXCEPT !.key = val] 
                  ELSE dict
       /\ ret' = IF dict[key] = NULL THEN "ok" ELSE "error"
       /\ op' = NULL
       /\ args' = << >>

Next == \/ \E k \in Keys: \E v \in Values: InsertReq(k, v)
        \/ InsertResp

vars == <<op, args, ret, dict>>

Spec == Init /\ [Next]_vars
====