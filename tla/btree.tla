---- MODULE btree ----
(*************************************************************
Technically, a B+ tree

We model as a set of nodes, and functions that describe things about them.

We need some node to initially be the root.
We can pick one arbitrarily.

For children, we need pairs with:
[maxKey, node]

There's also one pair with maxKey of NIL, which indicates that it's the unbounded one

Note that all keys are strictly less than "maxKey", so maxKey isn't the best name.
But I can't think of a better one.

**************************************************************)
EXTENDS TLC, Naturals

CONSTANTS Vals, Missing, Kmax, Nmax

Keys == 1..Kmax
Nodes == 1..Nmax

VARIABLES isLeaf,
          eltsOf, \* set of (key,val) pairs, for leaf nodes
          childrenOf, \*  set of (topKey,child) pairs of a node, except the last one, for non-leaf nodes
          lastOf, \* the last child of a node
          root,
          op,
          args,
          state,
          ret

Ops == {"get", "insert", "delete", "update"}
States == {"ready"}

NIL == CHOOSE NIL : NIL \notin Nodes \union Ops \union Keys \union Vals


TypeOK ==
    /\ isLeaf \in [Nodes -> {TRUE, FALSE}]
    /\ childrenOf \in [Nodes -> SUBSET {[topKey|->k, node|->n]: k \in Keys, n \in Nodes}]
    /\ lastOf \in [Nodes -> Nodes \union {NIL}]
    /\ eltsOf \in [Nodes -> SUBSET {[key|->k, val|->v]: k \in Keys, v \in Vals}]
    /\ root \in Nodes
    /\ op \in Ops 
    /\ state \in States

Init == /\ isLeaf = [n \in Nodes |-> TRUE] \* for simplicity, we init all nodes to leaves
        /\ childrenOf = [n \in Nodes |-> {}]
        /\ lastOf = [n \in Nodes |-> NIL]
        /\ eltsOf = [n \in Nodes |-> {}]
        /\ root = CHOOSE n \in Nodes : TRUE 
        /\ op = NIL
        /\ state = "ready"

\* Assumes non-empty set of children
MaxTopKeyOf(node) == 
    LET topKeys == {x.topKey: x \in childrenOf[node]}
    IN CHOOSE max \in topKeys : \A k \in topKeys \ {max}: max > k

\* Child that matches the key. Assumes a match exists
MatchingChild(children, key) ==
    LET topKeys == {x.topKey: x \in children}
        \* match is the closest one that goes over
        match == CHOOSE match \in topKeys : 
            /\ match > key
            /\ \A k \in topKeys \ {match} : k > key => k > match
    IN  CHOOSE child \in children: child.topKey = match


\* Given an inner node, find the child node to follow to obtain the key
\* assunes the node is a non-leaf
ChildNodeFor(node, key) ==
    CASE childrenOf[node] = {}     -> lastOf[node]
      [] MaxTopKeyOf(node) >= key  -> lastOf[node]
      [] OTHER                     -> MatchingChild(childrenOf[node], key).node


GetReq(key) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<key>>
    /\ state' = "getting"
    /\ ret' = NIL
    /\ UNCHANGED <<isLeaf, eltsOf, childrenOf, lastOf, root, op>>

RECURSIVE Get(_, _)
Get(key, node) ==
    IF isLeaf[node] THEN 
        LET keys == {e.key : e \in eltsOf[node]}
            elt == CHOOSE elt \in eltsOf[node] : elt.key = key
        IN IF key \in keys THEN elt.val ELSE Missing
    ELSE  Get(key, ChildNodeFor(node, key))

GetResp ==
    /\ state = "getting"
    /\ state' = "ready"
    /\ ret' = Get(args[1], root)
    /\ UNCHANGED <<isLeaf, eltsOf, childrenOf, lastOf, root, op>>


Next == \/ \E key \in Keys: GetReq(key)
        \/ GetResp

vars == <<isLeaf, eltsOf, childrenOf, lastOf, root, op, args, state, ret>>

Spec == Init /\ [Next]_vars

====