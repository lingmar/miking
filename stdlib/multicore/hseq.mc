include "multicore/pseq.mc"
include "mexpr/tuning/decision-points-boot.mc"

let hmap = lam f. lam seq.
  if (hole (Boolean {default = true, depth = 1})) then
    map f seq
  else
    pmap f seq

let hfold = lam f. lam acc. lam seq.
  if (hole (Boolean {default = true, depth = 1})) then
    foldl f acc seq
  else
    pfold f acc seq

let hiter = lam f. lam seq.
  if (hole (Boolean {default = true, depth = 1})) then
    iter f seq
  else
    piter f seq

mexpr
(hmap, hfold, hiter)
