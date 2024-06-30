(*

# Operations

* get
* insert
* update
* delete

## get
Return NULL if the key is not in the store

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

GetReq(key) == 
    /\ op = NULL
    /\ op' = "get"
    /\ args' = <<key>>
    /\ ret' = NULL
    /\ UNCHANGED <<ret, dict>>

GetResp ==
    /\ op = "get"
    /\ op' = NULL
    /\ args' = <<>>
    /\ LET key == args[1] 
        IN ret' = dict[key]
    /\ UNCHANGED dict

InsertReq(key, val) ==
    /\ op = NULL
    /\ op' = "insert"
    /\ args' = <<key, val>> 
    /\ ret' = NULL
    /\ UNCHANGED dict

InsertResp == 
    LET key == args[1]
        val == args[2] 
    IN /\ op = "insert"
       /\ dict' = IF dict[key] = NULL 
                  THEN [dict EXCEPT ![key] = val] 
                  ELSE dict
       /\ ret' = IF dict[key] = NULL THEN "ok" ELSE "error"
       /\ op' = NULL
       /\ args' = <<>>

UpdateReq(key, val) ==
    /\ op = NULL
    /\ op' = "update"
    /\ args' = <<key, val>>
    /\ ret' = NULL
    /\ UNCHANGED dict

UpdateResp ==
    LET key == args[1]
        val == args[2]
    IN /\ op = "update"
       /\ dict' = IF dict[key] # NULL
                  THEN [dict EXCEPT ![key]=val]
                  ELSE dict
      /\ ret' = IF dict[key] # NULL THEN "ok" ELSE "error"
      /\ op' = NULL
      /\ args' = <<>>
    
DeleteReq(key) ==
    /\ op = NULL
    /\ op' = "delete"
    /\ args = <<key>>
    /\ ret' = NULL
    /\ UNCHANGED dict

DeleteResp ==
    LET key == args[1]
    IN /\ op = "delete"
       /\ dict' = [dict EXCEPT ![key]=NULL]
       /\ op' = NULL
       /\ args' = <<>>

Next == \/ \E k \in Keys: GetReq(k)
        \/ GetResp
        \/ \E k \in Keys: \E v \in Values: InsertReq(k, v)
        \/ InsertResp
        \/ \E k \in Keys: \E v \in Values: UpdateReq(k, v)
        \/ UpdateResp
        \/ \E k \in Keys: DeleteReq(k)
        \/ DeleteResp


vars == <<op, args, ret, dict>>

Spec == Init /\ [Next]_vars

\* invariants

NeverErrors == ret # "error"
====