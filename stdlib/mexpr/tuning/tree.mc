
include "seq.mc"
include "common.mc"

type Tree
con Node : { root : a, children : [Tree]} -> Tree
con Leaf : Unit -> Tree

let treeEmpty = lam sentinel.
  Node {root = sentinel, children = []}

let treeInsert = lam eq. lam tree. lam path.
  match tree with Node t then
    let n = length path in
    recursive let insert = lam children. lam i.
      if eqi i n then
        cons (Leaf ()) children
      else
        let p = get path i in
        match partition (lam c.
          match c with Node {root = root} then eq root p
          else false) children
        with (equal, notEqual) then
          if eqi (length notEqual) (length children) then
            -- root not among children
            let newNode = Node {root = p, children = insert [] (addi i 1)} in
            cons newNode children
          else
            -- root is already among children
            match equal with [node] then
              match node with Node {root = root, children = cs} then
                let node = Node {root = root, children = insert cs (addi i 1)} in
                cons node notEqual
              else error "expected a node"
            else error "cannot match several roots"
        else never
    in Node {t with children = insert t.children 0}
else error "missing sentinel node"

let treeInsertMany = lam eq. lam tree. lam paths.
  foldl (treeInsert eq) tree paths

mexpr

let empty = treeEmpty 0 in

utest treeInsert eqi empty [] with Node {root = 0, children = [Leaf ()]} in
utest treeInsert eqi empty [1] with Node {root = 0, children = [Node {root = 1, children = [Leaf ()]}]} in
utest treeInsert eqi empty [1] with Node {root = 0, children = [Node {root = 1, children = [Leaf ()]}]} in

utest treeInsertMany eqi empty [[1],[1,2]]
with Node
{ root = 0
, children =
  [ Node {root = 1, children = [Node {root = 2, children = [Leaf ()]}, Leaf ()]} ]
} in

utest treeInsertMany eqi empty [[1],[1,2],[3]]
with Node
{ root = 0
, children =
[ Node {root = 3, children = [Leaf ()] }
, Node {root = 1, children = [Node {root = 2, children = [Leaf ()]}, Leaf ()]}
]
} in


()
