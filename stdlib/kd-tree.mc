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

let sqrti = lam a. floorfi (sqrtf (int2float a))

let timeDistSq = ref 0.0
let timeDistCmp = ref 0.0

-- Compute the squared distances between 'p1' and 'p2'
let distSq = lam p1. lam p2.
  let t1 = wallTimeMs () in
  let n = length p1 in
  recursive let dist = lam acc. lam p1. lam p2. lam i.
    if eqi i n then acc
    else
      let diff = subi (get p1 i) (get p2 i) in
      dist (addi acc (muli diff diff)) p1 p2 (addi i 1)
  in
  let d = dist 0 p1 p2 0 in
  let t2 = wallTimeMs () in
  modref timeDistSq (addf (deref timeDistSq) (subf t2 t1));
  d

utest distSq [0] [0] with 0
utest distSq [0,1] [1,2] with 2

let distCmp = lam p1. lam p2. lam limit.
  let t1 = wallTimeMs () in
  let n = length p1 in
  recursive let dist = lam acc. lam p1. lam p2. lam i.
    if eqi i n then
      if geqi acc limit then None () else Some acc
    else if geqi acc limit then None ()
    else
      let diff = subi (get p1 i) (get p2 i) in
      dist (addi acc (muli diff diff)) p1 p2 (addi i 1)
  in
  let d = dist 0 p1 p2 0 in
  let t2 = wallTimeMs () in
  modref timeDistCmp (addf (deref timeDistCmp) (subf t2 t1));
  -- utest
  --   let dSq = distSq ops p1 p2 in
  --   match d with None () then
  --     leqi limit dSq
  --   else match d with Some _ then
  --     gti limit dSq
  --   else never
  -- with true in
  d



utest distCmp [0] [0] 1 with Some 0
utest distCmp [0] [0] 0 with None ()
utest distCmp [0,1] [1,2] 3 with Some 2


let setNearest = lam p. lam nearest. lam dSq.
  let d = sqrti dSq in
  let min = map (lam x. subi x d) p in
  let max = map (addi d) p in
  { nearest = nearest, dSq = dSq, min = min, max = max}

utest setNearest [0] [1] 1
with {nearest = [1], dSq = 1, min = [subi 0 1], max = [1]}

utest setNearest [0,0] [1,1] 2
with {nearest = [1,1], dSq = 2, min = [subi 0 1, subi 0 1], max = [1,1]}

utest setNearest [438,681] [207,313] 188785
with {nearest = [207,313], dSq = 188785, min = [4,247], max = [872,1115]}

-- Find the nearest neighbor to a given point
let kdTreeNearest =
  lam k : Int.
  lam tree : KDTree v.
  lam point : Point v.
    recursive let work = lam curBest : Option (Nearest v). lam depth : Int. lam tree : KDTree v.
      let axis = modi depth k in
      match tree with Leaf p then
        match curBest with None () then
          let res = setNearest point p (distSq point p) in
          res
        else match curBest with Some best then
          let best : Nearest = best in
          let dcmp = distCmp point p best.dSq in
          match dcmp with Some dSq then
            setNearest point p dSq
          else match dcmp with None () then best
          else never
        else never
      else match tree with Node {split = split, left = left, right = right} then
        -- No first estimate yet found
        match curBest with None () then
          let v = get point axis in
          if lti v split then
            let best = work curBest (addi depth 1) left in
            if eqi best.dSq 0 then best else
            let maxSplit = get best.max axis in
            if leqi split maxSplit then
              -- There might be a closer point in right sub-tree
              work (Some best) (addi depth 1) right
            else best
          else
            let best = work curBest (addi depth 1) right in
            if eqi best.dSq 0 then best else
            let minSplit = get best.min axis in
            if gti split minSplit then
              -- There might be a closer point in left sub-tree
              work (Some best) (addi depth 1) left
            else best
        -- We have an estimate already
        else match curBest with Some best then
          let best : Nearest = best in
          if eqi best.dSq 0 then best else
          let minSplit = get best.min axis in
          let best =
            if gti split minSplit then
              work (Some best) (addi depth 1) left
            else best
          in
          if eqi best.dSq 0 then best else
          let maxSplit = get best.max axis in
          if leqi split maxSplit then
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

let nearest : Nearest Int = kdTreeNearest 2 tree [438, 681] in

utest nearest.nearest with [343, 858] in

()
