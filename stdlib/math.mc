include "ext/math-ext.mc"

-- Float stuff
let inf = divf 1.0 0.0
let minf = lam r. lam l. if ltf r l then r else l

utest minf 0. 0. with 0. using eqf
utest minf 1. 0. with 0. using eqf
utest minf 0. 1. with 0. using eqf

utest absf 0. with 0. using eqf
utest absf 1. with 1. using eqf
utest absf (negf 1.) with 1. using eqf

-- Int stuff
let maxi = lam r. lam l. if gti r l then r else l
let mini = lam r. lam l. if lti r l then r else l
let absi = lam i. maxi i (negi i)
let sqrti = lam n.
  recursive let work = lam n.
    match n with 1 then 1
    else
      let nn = work (subi n 1) in
      divi (addi nn (divi n nn)) 2
  in
  match n with 0 then 0
  else if gti n 0 then work n
  else error "sqrti of a negative number"

utest maxi 0 0 with 0
utest maxi 1 0 with 1
utest maxi 0 1 with 1

utest mini 0 0 with 0
utest mini 1 0 with 0
utest mini 0 1 with 0

utest absi 0 with 0
utest absi 1 with 1
utest absi (negi 1) with 1

utest addi 1 (negi 1) with 0

utest sqrti 0 with 0
utest sqrti 1 with 1
utest sqrti 2 with 1
utest sqrti 4 with 2
