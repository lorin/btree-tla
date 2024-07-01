---- MODULE btree ----
(*************************************************************
Technically, a B+ tree

A node is a structure that 
* indicate it's a leaf
* has a list of entries

The entries are key, val structs. The key is always an index.
The value depends on whether it's a leaf or not.

If it's a leaf, the value is the actual data to be returned.
If it's an inner node, it points to the next structure


Finding an element means:



**************************************************************)
EXTENDS TLC, Sequences

CONSTANTS Keys, Vals, NIL

MISSING == CHOOSE x : x \notin Vals

VARIABLES root

FindValInLeaf(key, node) ==
    LET RECURSIVE Helper(_)
    Helper(elts) == 
        CASE elts = << >>        -> MISSING
          [] Head(elts)[1] = key -> Head(elts)[2]
          [] OTHER               -> Helper(Tail(elts))
    IN Helper(node.entries)

Init == 
    /\ root = [leaf |-> TRUE, entries |-> {}, tail |-> NIL]


IsValidEntry(e) ==
    /\ DOMAIN e == {"key", "val"}
    /\ e.key \in Keys

IsValidLeafEntry(e) ==
    /\ IsValidEntry(e)
    /\ e.val \in Vals

RECURSIVE IsValidTree(_)
IsValidTree(node) ==
    /\ DOMAIN node = {"leaf", "entries", "tail"}
    /\ node.leaf \in {TRUE, FALSE}
    /\ node.leaf = TRUE => node.tail = NIL /\ \A e \in entries: IsValidLeafEntry(e)
    /\ node.leaf = FALSE => /\ IsValidTree(node.tail)
                            /\ \A e \in entries : IsValidEntry(e) /\ IsValidTree(e.val)


TypeOK == IsValidTree(root)



MaxKey(node) == 
    LET entry = 
        CHOOSE x \in node.entries : \A y \in entries \ {x} : x.key > y.key
    IN entry.key


\* Given a non-inner node, find the appropriate child node
\* The child is the smallest entry that is greater than the key.
\* Assumes it exists
FindChildEntry(key, entries) == 
    CHOOSE x \in entries: /\ x.key > key 
                          /\ \A y \in entries \ {x} : y.key > key => x.key < y.key


FindChild(key, node) == 
    IF node.entries = {} THEN node.tail ELSE FindChildEntry(key, node.entries).val

RECURSIVE FindRecursive(_, _)
FindRecursive(key, node) ==
    IF node.leaf THEN FindValInLeaf(key, node) ELSE FindRecursive(key, FindChild(key, node))

Find(key) == FindRecursive(key, root)
    


====