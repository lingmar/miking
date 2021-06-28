
include "benchmarkcommon.mc"
include "string.mc"
include "common.mc"
include "mapn.ml"
include "multicore/pseq.mc"

mexpr

recursive
let fact = lam n.
  if eqi n 0
  then 1
  else muli n (fact (subi n 1))
in

let mapf = lam n.
  pmap (lam. fact 50) (createRope n (lam i. i))
in

-- iter (lam x. print (int2string x)) (mapf n);

repeat (lam. mapf n)
