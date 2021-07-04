include "common.mc"
include "math.mc"

-- TODO: duplicate points

-- Implements a k-dimensional tree (k-d tree)

type KDTree v
con Node : {split : v, left : KDTree v, right : KDTree v} -> KDTree v
con Leaf : [v] -> KDTree v

type Point a = [a]

-- Insert all elements up-front (guarantees a balanced tree)
let kdTreeCreate : (v -> v -> Int) -> Int -> [Point v] -> KDTree v =
  lam cmp. lam k. lam points.
    recursive let work = lam points. lam depth.
      let medianIdx = divi (length points) 2 in
      match points with [] then error "empty points"
      else match points with [p] then Leaf p
      else
        let axis = modi depth k in
        let sorted = mergeSort (lam p1. lam p2.
          cmp (get p1 axis) (get p2 axis)) points in
        match splitAt sorted medianIdx with (smaller, greaterEq) then
          let medianPoint = head greaterEq in
          let left = work smaller (addi depth 1) in
          Node { split = get medianPoint axis
               , left = work smaller (addi depth 1)
               , right = work greaterEq (addi depth 1)
               }
        else never
    in
    work points 0

type Nearest v = {nearest : Point v, dSq : v, min : Point v, max : Point v}

type NumOps v =
{ zero : v
, add : v -> v -> v
, sub : v -> v -> v
, cmp : v -> v -> Int
, mul : v -> v -> v
, sqrtFun : v -> v
}

let intOps : NumOps Int =
{ zero = 0
, add = addi
, sub = subi
, cmp = subi
, mul = muli
, sqrtFun = lam a. floorfi (sqrtf (int2float a))
--, sqrtFun = sqrti
}

-- Compute the squared distances between 'p1' and 'p2'
let distSq = lam ops : NumOps v. lam p1. lam p2.
  let dists = zipWith (lam x. lam y.
    let diff = ops.sub x y in
    ops.mul diff diff
  ) p1 p2 in
  foldl ops.add ops.zero dists

utest distSq intOps [0] [0] with 0
utest distSq intOps [0,1] [1,2] with 2

let setNearest = lam ops : NumOps. lam p. lam nearest. lam dSq.
  match ops with { zero = zero, add = add, sub = sub, mul = mul, sqrtFun = sqrtFun }
  then
    let ps = zipWith (lam p. lam q. (p,q)) p nearest in
    let d = sqrtFun dSq in
    let min = map (lam x. sub x d) p in
    let max = map (add d) p in
    { nearest = nearest, dSq = dSq, min = min, max = max}
  else never

utest setNearest intOps [0] [1] 1
with {nearest = [1], dSq = 1, min = [subi 0 1], max = [1]}

utest setNearest intOps [0,0] [1,1] 2
with {nearest = [1,1], dSq = 2, min = [subi 0 1, subi 0 1], max = [1,1]}

utest setNearest intOps [438,681] [207,313] 188785
with {nearest = [207,313], dSq = 188785, min = [4,247], max = [872,1115]}

-- Find the nearest neighbor to a given point
let kdTreeNearest =
  lam ops : NumOps v.
  lam k : Int.
  lam tree : KDTree v.
  lam point : Point v.
    recursive let work = lam curBest : Option (Nearest v). lam depth : Int. lam tree : KDTree v.
      let axis = modi depth k in
      match tree with Leaf p then
        match curBest with None () then
          -- print "point: "; iter dprintLn point;
          -- print "nearest: "; iter dprintLn p;
          let res = setNearest ops point p (distSq ops point p) in
          -- printLn "After nearest";
          res
        else match curBest with Some best then
          let best : Nearest = best in
          let dSq = distSq intOps point p in
          if lti (ops.cmp dSq best.dSq) 0 then
            setNearest ops point p dSq
          else best
        else never
      else match tree with Node {split = split, left = left, right = right} then
        -- No first estimate yet found
        match curBest with None () then
          let v = get point axis in
          if lti (ops.cmp v split) 0 then
            let best = work curBest (addi depth 1) left in
            let maxSplit = get best.max axis in
            if leqi (ops.cmp split maxSplit) 0 then
              -- There might be a closer point in right sub-tree
              work (Some best) (addi depth 1) right
            else best
          else
            let best = work curBest (addi depth 1) right in
            let minSplit = get best.min axis in
            if gti (ops.cmp split minSplit) 0 then
              -- There might be a closer point in left sub-tree
              work (Some best) (addi depth 1) left
            else best
        -- We have an estimate already
        else match curBest with Some best then
          let best : Nearest = best in
          let minSplit = get best.min axis in
          let best =
            if gti (ops.cmp split minSplit) 0 then
              work (Some best) (addi depth 1) left
            else best
          in
          let maxSplit = get best.max axis in
          if leqi (ops.cmp split maxSplit) 0 then
            work (Some best) (addi depth 1) right
          else best
        else never
      else never
    in
    work (None ()) 0 tree

mexpr

let points =
[ [615, 40]
, [70, 721]
, [888, 585]
, [343, 858]
, [207, 313]
, [751, 177]
, [479, 449]
] in

let tree = kdTreeCreate subi 2 points in

let nearest : Nearest Int = kdTreeNearest intOps 2 tree [438, 681] in

utest nearest.nearest with [343, 858] in

()
