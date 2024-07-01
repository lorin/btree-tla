---- MODULE btree ----
(*************************************************************
Technically, a B+ tree

We model as a set of nodes, and functions that describe things about them.

We need some node to initially be the root.
We can pick one arbitrarily. 


**************************************************************)
EXTENDS TLC, Sequences

CONSTANTS Nodes, NIL, 

VARIABLE IsLeaf, 
        root
        

Init ==
    /\ IsLeaf = [n : Nodes |-> TRUE] \* set all nodes as leaves initially
    /\ root = CHOOSE n \in Node 

Get(key) == 
    IF IsLeaf[root] THEN 

    

TypeOK ==
    /\ IsLeaf \in [Nodes -> {TRUE, FALSE}]
    /\ root \in Nodes


====