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

CONSTANTS Nodes, Keys, Vals, Missing, N

VARIABLES IsLeaf,
          ValuesOf,
          root

TypeOK ==
    /\ IsLeaf \in [Nodes -> {TRUE, FALSE}]
    /\ ValuesOf \in [Nodes -> Entries ]
    /\ root \in Nodes
k

Entries == {[key|-> k, val|->v]: k \in Keys, v \in Vals]}
Children == {[maxKey|->k, node|->n]: k \in Keys}

KeysOf(entries) == {e.k : e \in entries}

Init == /\ IsLeaf = [n : Nodes |-> TRUE] \* for simplicity, we init all nodes to leaves
        /\ root = CHOOSE n \in Node


\* Given an inner node, find the child node to follow to obtain the key
ChildNodeFor(node, key) ==
    \* First,



Get(key) == LET
    RECURSIVE Helper(_)
    Helper(node) ==
        IF IsLeaf[node] THEN
            IF k \in KeysOf(EntriesOf[node]) THEN LET
                e == CHOOSE e \in EntriesOf[node] : e.k = key IN e.val
            ELSE Missing
        ELSE \* Recurse on the appropriate child node
            Helper(ChildNode(node, key))
    IN Helper(root)



====