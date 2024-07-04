---- MODULE btree ----
EXTENDS TLC,
        Naturals,
        FiniteSets,
        Sequences

CONSTANTS Vals,
          MaxKey,
          MaxNode,
          MaxOccupancy,

          \* ops
          INSERT,

          \* states
          READY,
          WHICH_TO_SPLIT,
          ADD_TO_LEAF

Keys == 1..MaxKey
Nodes == 1..MaxNode

NIL == CHOOSE x : x \notin Nodes

MISSING == CHOOSE v : v \notin Vals


VARIABLES root,
          isLeaf,
          keysOf,
          childOf,
          lastOf,
          valOf,
          focus,
          toSplit,
          op,
          state

TypeOk == /\ root \in Nodes
          /\ isLeaf \in [Nodes -> BOOLEAN]
          /\ keysOf \in [Nodes -> SUBSET Keys]
          /\ childOf \in [Nodes \X Keys -> Nodes \union {NIL}]
          /\ lastOf \in [Nodes -> Nodes \union {NIL}]
          /\ focus \in Nodes \union {NIL}
          /\ toSplit \in Seq(Nodes)
          /\ op \in {INSERT}
          /\ state \in {READY, WHICH_TO_SPLIT, ADD_TO_LEAF}

\* Max element in a set
Max(xs) == CHOOSE x \in xs : \A y \in xs : x > y

\* Find the appropriate child node associated with the key
ChildNodeFor(node, key) ==
    LET keys == keysOf[node]
        maxKey == Max(keys)
        closestKey == CHOOSE k \in keys : k>key /\ ~\E j \in keys - {k} : j>key /\ j<k
    IN IF key > maxKey 
       THEN lastOf[node] 
       \* smallest k that's bigger than key
       ELSE childOf[<<node, closestKey>>]

\* Identify the leaf node based on key
\* Find the leaf node associated with a key
RECURSIVE FindLeafNode(_, _)
FindLeafNode(node, key) ==
    IF isLeaf[node]
    THEN node
    ELSE FindLeafNode(ChildNodeFor(node, key), key)
    

AtMaxOccupancy(node) == Cardinality(keysOf[node]) = MaxOccupancy

(*)
InsertReq(key, val) ==
    LET leaf == FindLeafNode(root, key)
    /\ state = READY
    /\ op = INSERT
    /\ focus' = leaf
    /\ state = IF AtMaxOccupancy(leaf) THEN WHICH_TO_SPLIT ELSE ADD_TO_LEAF

\* We model a "free" (not yet part of the tree) node as one as a leaf with no keys
IsFree(node) == isLeaf[node] /\ keysOf[node] = {}

Init == /\ root = CHOOSE n \in Nodes : isFree(node)
        /\ isLeaf = [n \in Nodes |-> TRUE]
        /\ keysOf = [n \in Nodes |-> {}]
        /\ childOf = [n \in Nodes, k \in Keys |-> NIL]
        /\ lastOf = [n \in Nodes |-> NIL]
        /\ focus = NIL
        /\ toSplit = <<>>
        /\ op = NIL
        /\ state = READY

Next == /\ \E k \in Keys, v \in Vals : InsertReq(key, val)
*)

====