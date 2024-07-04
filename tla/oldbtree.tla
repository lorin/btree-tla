---- MODULE oldbtree ----
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

CONSTANTS Vals, Missing, Kmax, Nmax, MaxLeafSize, MaxInnerSize

Keys == 1..Kmax
Nodes == 1..Nmax

VARIABLES isLeaf,
          eltsOf, \* set of (key,val) pairs, for leaf nodes
          childrenOf, \*  set of (topKey,child) pairs of a node, except the last one, for non-leaf nodes
          lastOf, \* the last child of a node
          root,

          \* function interface
          op,
          args,
          ret,

          \*
          \* local variables
          \*
          state,
          insertLeafTarget,
          tooBigInner,

          \* When there's a split
          smallerSplit,
          largerSplit,
          minLarger \* smallest key in the larger split
          

Ops == {"get", "insert", "delete", "update"}
States == {"ready", 
           "getting",
           "inserting-into-leaf",
           "splitting-leaf",
           "splitting-inner"}

NIL == CHOOSE NIL : NIL \notin Nodes \* \union Ops \union Keys \union Vals



TypeOK ==
    /\ args \in {<<k>>: k \in Keys} \union {<<k,v>>: k \in Keys, v \in Vals} \union {NIL}
    /\ childrenOf \in [Nodes -> SUBSET {[topKey|->k, node|->n]: k \in Keys, n \in Nodes}]
    /\ eltsOf \in [Nodes -> SUBSET {[key|->k, val|->v]: k \in Keys, v \in Vals}]
    /\ isLeaf \in [Nodes -> {TRUE, FALSE}]
    /\ \A n \in Nodes: lastOf[n] \in Nodes
    /\ root \in Nodes
    /\ op \in Ops \union {NIL}
    /\ state \in States
    /\ insertLeafTarget \in Nodes
    /\ tooBigInner \in Nodes
    
    
Init == /\ isLeaf = [n \in Nodes |-> TRUE] \* for simplicity, we init all nodes to leaves
        /\ childrenOf = [n \in Nodes |-> {}]
        /\ lastOf = [n \in Nodes |-> CHOOSE x \in Nodes: TRUE] \* we don't care what this is initialized to
        /\ eltsOf = [n \in Nodes |-> {}]
        /\ root = CHOOSE n \in Nodes : isLeaf[n] /\ eltsOf[n] = {}
        /\ op = NIL
        /\ args = NIL
        /\ ret = NIL
        /\ state = "ready"
        /\ insertLeafTarget = CHOOSE n \in Nodes : TRUE  \* don't care
        /\ tooBigInner = CHOOSE n \in Nodes : TRUE \* dont' care


\* Assumes non-empty set of children
MaxTopKeyOf(children) == 
    LET topKeys == {x.topKey: x \in childrenOf[children]}
    IN CHOOSE max \in topKeys : \A k \in topKeys \ {max}: max > k

MinTopKeyOf(children) == 
    LET topKeys == {x.topKey: x \in childrenOf[children]}
    IN CHOOSE min \in topKeys : \A k \in topKeys \ {min}: min < k

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
    LET kids == childrenOf[node] IN
    CASE kids = {}    -> lastOf[node] 
      [] key >= MaxTopKeyOf(kids) -> lastOf[node]
      [] OTHER                    -> MatchingChild(childrenOf[node], key).node


GetReq(key) ==
    /\ state = "ready"
    /\ op' = "get"
    /\ args' = <<key>>
    /\ state' = "getting"
    /\ ret' = NIL
    /\ UNCHANGED <<isLeaf, eltsOf, childrenOf, lastOf, root, insertLeafTarget, tooBigInner>>

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
    /\ UNCHANGED <<isLeaf, eltsOf, childrenOf, lastOf, root, op, args, insertLeafTarget, tooBigInner>>

InsertReq(key, val) ==
    /\ state = "ready"
    /\ op' = "insert"
    /\ args' = <<key, val>> 
    /\ ret' = NIL
    /\ state' = "inserting-into-leaf"
    /\ UNCHANGED <<isLeaf, eltsOf, childrenOf, lastOf, root, insertLeafTarget, tooBigInner>>

IsPresent(leaf, key) == key \in {e.key : e \in eltsOf[leaf]}

\* initially, just assume a leaf can handle an infinite amount
\* This is a non-interesting B-tree, but behavior should be 
\* correct, and we can alter this later
IsLeafTooBig(leaf) == Cardinality(eltsOf[leaf]) > MaxLeafSize

IsInnerTooBig(node) == Cardinality(childrenOf[node]) > MaxInnerSize

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
       /\ UNCHANGED <<isLeaf, childrenOf, lastOf, root, op, args, tooBigInner>>


ChildNodesOf(node) == {e.node: e \in childrenOf[node]} \union {lastOf[node]}

\* Return parent of non-root node
ParentOf(node) == CHOOSE p \in Nodes : node \in ChildNodesOf(p)
(**************
 Remove the larger half of the leaf entries.
 New leaf node should contain the larger half.
 We also make the larger half "larger" in cardinality if it's odd, just for convenience

***************)

\** Check if a node is the "last" element with respect to its parent
IsLast(node) == lastOf[ParentOf(node)] = node

\** Check if a node has not yet been allocated for use yet
IsUnused(node) == isLeaf[node] /\ eltsOf[node] = {}


SplitLeaf ==
    LET elts == eltsOf[insertLeafTarget]
        largerHalf == CHOOSE s \in SUBSET elts : /\  \/ Cardinality(s) = Cardinality(elts \ s)
                                                     \/ Cardinality(s) = Cardinality(elts \ s) + 1
                                                 /\ \A x \in s, y \in elts \ s : x.key>y.key
        smallerHalf == elts \ largerHalf
        oldLeaf == insertLeafTarget
        newLeaf == CHOOSE n \in Nodes : IsUnused(n)
        keysInLarger == {n.key : n \in largerHalf}
    IN  
    /\ state = "splitting-leaf"
    /\ smallerSplit' = oldLeaf
    /\ largerSplit' = newLeaf
    /\ minLarger = CHOOSE key \in keysInLarger: \A x \in keysInLarger \ {key}: key<x
    /\ eltsOf' = [eltsOf EXCEPT ![oldLeaf]=smallerHalf, ![newLeaf]=largerHalf]
    /\ childrenOf' = IF oldLeaf # root 
    
    [childrenOf EXCEPT ![ParentOf(oldLeaf)]=@ \union {[]}]
    /\ lastOf' = IF oldLeaf # root /\ IsLast(oldLeaf) THEN [lastOf EXCEPT ![ParentOf(oldLeaf)]=newLeaf] ELSE lastOf
    /\ tooBigInner' = IF oldLeaf # root      
                      THEN ParentOf(oldLeaf) \* We may not need to resize this, but just in case, we store it
                      ELSE tooBigInner \* We don't care, since there's no parent
    /\ ret' = 
        CASE oldLeaf = root              -> "adding-root" 
          [] IsInnerTooBig(tooBigInner)' -> ret   
          [] OTHER                       -> "ok"  \* we're done
    /\ state' = 
        CASE oldLeaf = root              -> "creating-new-root" \* need to create a new root
          [] IsInnerTooBig(tooBigInner)' -> "splitting-inner"   \* too big, we'll need to split
          [] OTHER                       -> "ready"
    /\ UNCHANGED <<op, args, insertLeafTarget, root, isLeaf>>


\* If the root was split, we need to add a new root
CreatingNewRoot ==
    LET newRoot == CHOOSE n \in Nodes : IsUnused(n) IN 
    /\ root' = newRoot
    /\ isLeaf' = [isLeaf EXCEPT ![newRoot]=FALSE]
    /\ childrenOf' = [childrenOf EXCEPT ![newRoot]={[topKey|->minLarger, node|->smallerSplit]}]
    /\ lastOf' = [lastOf EXCEPT ![newRoot]=largerSplit]
    /\ ret' = "ok"
    /\ state' = "ready"
    /\ UNCHANGED <<op, args, eltsOf, insertLeafTarget, tooBigInner, smallerSplit, largerSplit, minLarger>>

SplitInner ==
    LET kids == childrenOf[tooBigInner]
        largerHalf == CHOOSE s \in SUBSET kids: /\ \/ Cardinality(s)     = Cardinality(kids \ s)
                                                   \/ Cardinality(s) + 1 = Cardinality(kids) \* The larger will get an extra due to "last", so bias away from it
        smallerHalf == kids \ largerHalf
        maxTopKeySmallerHalf == MaxTopKeyOf(smallerHalf)
        maxChildSmallerHalf == CHOOSE kid \in smallerHalf : kid.topKey = maxTopKeySmallerHalf
        minTopKeyLargerHalf == MinTopKeyOf(largerHalf)
        oldNode == tooBigInner
        newNode == CHOOSE n \in Nodes : IsUnused(n) 
        parent == ParentOf(oldNode) 
        parentChildEntry == CHOOSE x \in childrenOf[parent] : x.node=oldNode
        originalTopKey == parentChildEntry.topKey
        smallerParentChildEntry == [topKey|->minTopKeyLargerHalf, node|->oldNode]
        largerParentChildEntry == [topKey|->originalTopKey, node|->newNode]
        childrenOfPrime == [childrenOf EXCEPT ![oldNode]=smallerHalf \ {maxChildSmallerHalf}, ![newNode]=largerHalf]
     IN
    /\ state = "splitting-inner"
    /\ smallerSplit' = oldNode
    /\ largerSplit' = newNode
    /\ minLarger' = minTopKeyLargerHalf \** I'm not 100% sure of this
    /\ isLeaf' = [isLeaf EXCEPT ![newNode]=FALSE]
    /\ childrenOf' = 
        CASE oldLeaf = root  -> childrenOfPrime \* next stage will update it
          [] IsLast(oldLeaf) -> [childrenOfPrime EXCEPT ![parent]=@ \union {smallerParentChildEntry}]
          [] OTHER           -> [childrenOfPrime EXCEPT ![parent]=(@ \union {smallerParentChildEntry, largerParentChildEntry}) \ {parentChildEntry}]
       \* This only needs updating if we split the last element
    /\ lastOf' = IF IsLast(oldLeaf) THEN [lastOf EXCEPT ![parent]=newNode] ELSE lastOf
    /\ tooBigInner' = IF oldLeaf # root      
                      THEN ParentOf(oldLeaf) \* We may not need to resize this, but just in case, we store it
                      ELSE tooBigInner \* We don't care, since there's no parent
    /\ ret' = 
        CASE oldLeaf = root              -> "adding-root" 
          [] IsInnerTooBig(tooBigInner)' -> ret   
          [] OTHER                       -> "ok"  \* we're done
    /\ state' = 
        CASE oldLeaf = root              -> "creating-new-root" \* need to create a new root
          [] IsInnerTooBig(tooBigInner)' -> "splitting-inner"   \* too big, we'll need to split
          [] OTHER                       -> "ready"
    /\ UNCHANGED <<eltsOf, root, op, args, insertLeafTarget, tooBigInner>>



Next == \/ \E key \in Keys: GetReq(key)
        \/ GetResp
        \/ \E key \in Keys, val \in Vals: InsertReq(key, val)
        \/ InsertIntoLeaf
        \/ SplitLeaf
        \/ SplitInner

vars == <<isLeaf, eltsOf, childrenOf, lastOf, root, op, args, state, ret>>

Spec == Init /\ [Next]_vars

\* Invariants

NoDuplicateEntries ==
    \A x,y \in Nodes : (eltsOf[x] \intersect eltsOf[y] # {}) => x=y

WhenRootIsLeafNoOtherNodesShouldHaveELements ==
    isLeaf[root] => \A n \in Nodes \ {root} : eltsOf[n] = {}

====
