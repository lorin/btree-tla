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
EXTENDS TLC, Naturals, FiniteSets

CONSTANTS Vals, Missing, Kmax, Nmax, MaxLeafSize, MaxNonLeafSize

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
          ret,
          insertLeafTarget,
          expandedInnerNode
          

Ops == {"get", "insert", "delete", "update"}
States == {"ready", 
           "getting",
           "inserting-into-leaf",
           "splitting-leaf",
           "splitting-inner"}

NIL == CHOOSE NIL : NIL \notin Nodes \union Ops \union Keys \union Vals


TypeOK ==
    /\ args \in {<<k>>: k \in Keys} \union {<<k,v>>: k \in Keys, v \in Vals} \union {NIL}
    /\ childrenOf \in [Nodes -> SUBSET {[topKey|->k, node|->n]: k \in Keys, n \in Nodes}]
    /\ eltsOf \in [Nodes -> SUBSET {[key|->k, val|->v]: k \in Keys, v \in Vals}]
    /\ isLeaf \in [Nodes -> {TRUE, FALSE}]
    /\ \A n \in Nodes: lastOf[n] = NIL \/ lastOf[n] \in Nodes
    /\ root \in Nodes
    /\ op \in Ops \union {NIL}
    /\ state \in States
    /\ insertLeafTarget \in Nodes
    /\ expandedInnerNode \in Nodes
    
    
Init == /\ isLeaf = [n \in Nodes |-> TRUE] \* for simplicity, we init all nodes to leaves
        /\ childrenOf = [n \in Nodes |-> {}]
        /\ lastOf = [n \in Nodes |-> NIL]
        /\ eltsOf = [n \in Nodes |-> {}]
        /\ root = CHOOSE n \in Nodes : isLeaf[n] /\ eltsOf[n] = {}
        /\ op = NIL
        /\ args = NIL
        /\ ret = NIL
        /\ state = "ready"
        /\ insertLeafTarget = CHOOSE n \in Nodes : TRUE  \* don't care
        /\ expandedInnerNode = CHOOSE n \in Nodes : TRUE \* dont' care


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
    /\ UNCHANGED <<isLeaf, eltsOf, childrenOf, lastOf, root, insertLeafTarget, expandedInnerNode>>

\* Find the leaf node associated with a key
RECURSIVE FindLeafNode(_, _)
FindLeafNode(node, key) ==
    IF isLeaf[node] 
    THEN node 
    ELSE FindLeafNode(ChildNodeFor(node, key), key)

\* Retrieve a key, starting from the root
Get(key) ==
    LET node == IF isLeaf[root] THEN root ELSE FindLeafNode(root, key)
        keys == {e.key : e \in eltsOf[node]}
        elt == CHOOSE elt \in eltsOf[node] : elt.key = key
    IN IF key \in keys 
       THEN elt.val 
       ELSE Missing

GetResp ==
    /\ state = "getting"
    /\ state' = "ready"
    /\ ret' = Get(args[1])
    /\ UNCHANGED <<isLeaf, eltsOf, childrenOf, lastOf, root, op, args, insertLeafTarget, expandedInnerNode>>

InsertReq(key, val) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<key, val>> 
    /\ ret' = NIL
    /\ state' = "inserting-into-leaf"
    /\ UNCHANGED <<isLeaf, eltsOf, childrenOf, lastOf, root, insertLeafTarget, expandedInnerNode>>

IsPresent(leaf, key) == key \in {e.key : e \in eltsOf[leaf]}

\* initially, just assume a leaf can handle an infinite amount
\* This is a non-interesting B-tree, but behavior should be 
\* correct, and we can alter this later
IsLeafTooBig(leaf) == Cardinality(eltsOf[leaf]) > MaxLeafSize

IsNonLeafTooBig(node) == Cardinality(childrenOf[node]) > MaxNonLeafSize

InsertIntoLeaf ==
    LET key == args[1] 
        val == args[2]
        leaf == FindLeafNode(root, key) 
    IN /\ state = "inserting-into-leaf"
       /\ insertLeafTarget' = leaf
       /\ eltsOf' = IF IsPresent(leaf, key) THEN eltsOf ELSE [eltsOf EXCEPT ![leaf] = @ \union {[key|->key, val|->val]}]
       /\ state' = 
        CASE IsPresent(leaf, key) -> "ready"
          [] IsLeafTooBig(insertLeafTarget)'  -> "splitting-leaf"
          [] OTHER                -> "ready"
       /\ ret' = 
        CASE IsPresent(leaf, key) -> "error"
          [] IsLeafTooBig(insertLeafTarget)'  -> ret \* not set yet
          [] OTHER                -> "ok"
       /\ UNCHANGED <<isLeaf, childrenOf, lastOf, root, op, args, expandedInnerNode>>


\* Return parent of non-root node
ParentOf(node) == CHOOSE p \in Nodes : childrenOf[p].node = node

(**************
 Remove the larger half of the leaf entries.
 New leaf node should contain the larger half.
 We also make the larger half "larger" in cardinality if it's odd, just for convenience

***************)

\** Check if a node is the "last" element with respect to its parent
IsLast(node) == lastOf[ParentOf(node)] = node


SplitLeaf ==
    LET elts == eltsOf[insertLeafTarget]
        largerHalf == CHOOSE s \in SUBSET elts : /\  \/ Cardinality(s) = Cardinality(elts \ s)
                                                      \/ Cardinality(s) = Cardinality(elts \ s) + 1
                                                  /\ \A x \in s, y \in elts \ s : x.key>y.key
        smallerHalf == elts \ largerHalf
        oldLeaf == insertLeafTarget
        newLeaf == CHOOSE n \in Nodes : isLeaf[n] /\ eltsOf[n] = {}
        newRoot == CHOOSE n \in Nodes : isLeaf[n] /\ eltsOf[n] = {} /\ n # newLeaf
        keysInLarger == {n.key : n \in largerHalf}
        minLarger == CHOOSE key \in keysInLarger: \A x \in keysInLarger \ {key}: key<x
        childEntry == [topKey|->minLarger, node|->oldLeaf]
    IN  
    /\ state = "splitting-leaf"
    (* TODO: I am here

I need to:
    - update the eltsOf for the old and new leaf
    - update the parent node
    - check if the parent needs splitting. Or, if we're a root, adding
    *)
    /\ eltsOf' = [eltsOf EXCEPT ![oldLeaf]=smallerHalf, ![newLeaf]=largerHalf]
    /\ root' = IF oldLeaf = root THEN newRoot ELSE root
    /\ isLeaf' = IF oldLeaf = root 
                 THEN [isLeaf EXCEPT ![oldLeaf]=FALSE] 
                 ELSE isLeaf
    /\ childrenOf' = IF oldLeaf = root 
                     THEN [childrenOf EXCEPT ![newRoot]={childEntry}]
                     ELSE [childrenOf EXCEPT ![ParentOf(oldLeaf)]=@ \union {childEntry}]
    /\ lastOf' = 
        CASE oldLeaf = root  -> [lastOf EXCEPT ![newRoot]=newLeaf]
          [] IsLast(oldLeaf) -> [lastOf EXCEPT ![ParentOf(oldLeaf)]=newLeaf]
    /\ expandedInnerNode' = IF oldLeaf = root THEN newRoot ELSE ParentOf(oldLeaf)
    /\ ret' = 
        CASE oldLeaf = root                      -> "ok"  \* we're done
          [] IsNonLeafTooBig(expandedInnerNode)' -> ret   \* not done yet
          [] OTHER                               -> "ok"  \* we're done
    /\ state' = 
        CASE oldLeaf = root                      -> "ready"           \* If we created a new root, there's no need to split
          [] IsNonLeafTooBig(expandedInnerNode)' -> "splitting-inner" \* too big, we'll need to split
          [] OTHER                               -> "ready"
    /\ UNCHANGED <<op, args, insertLeafTarget>>



Next == \/ \E key \in Keys: GetReq(key)
        \/ GetResp
        \/ \E key \in Keys, val \in Vals: InsertReq(key, val)
        \/ InsertIntoLeaf

vars == <<isLeaf, eltsOf, childrenOf, lastOf, root, op, args, state, ret>>

Spec == Init /\ [Next]_vars

====