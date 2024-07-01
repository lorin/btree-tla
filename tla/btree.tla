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

CONSTANTS Nodes, Keys, Vals, Missing 

VARIABLES IsLeaf,
          eltsOf \* set of (key,val) pairs, for leaf nodes
          childrenOf, \*  set of (topKey,child) pairs of a node, except the last one, for non-leaf nodes
          lastOf, \* the last child of a node
          root,

NIL == CHOOSE NIL : NIL \notin Nodes


TypeOK ==
    /\ isLeaf \in [Nodes -> {TRUE, FALSE}]
    /\ childrenOf \in [Nodes -> SUBSET {[topKey|->k, node|->n]: k \in Keys, n \in Nodes}]
    /\ lastOf \in [Nodes -> Nodes \union {NIL}]
    /\ eltsOf \in [Nodes -> SUBSET {[key|->k, val|->v]: k \in Keys, v \in Vals}]
    /\ root \in Nodes

Entries == {[key|-> k, val|->v]: k \in Keys, v \in Vals]}


Init == /\ isLeaf = [n : Nodes |-> TRUE] \* for simplicity, we init all nodes to leaves
        /\ childrenOf = [n : Nodes |-> {}]
        /\ lastOf = [n : Nodes |-> NIL]
        /\ eltsOf = [n : Nodes |-> {}]
        /\ root = CHOOSE n \in Node

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
    CASE childrenOf[node] = {}         -> lastOf[node]
      [] MaxTopKeyOfNode(node) >= key  -> lastOf[node]
      [] OTHER                         -> MatchingChild(childrenOf[node]).node

\*
\* TODO: Probably need to update this stuff here
KeysOf(entries) == {e.k : e \in entries}

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