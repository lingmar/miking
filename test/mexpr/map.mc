-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Map intrinstics

include "seq.mc"

mexpr

-- Int map
let m = mapEmpty subi in

let m = mapInsert 1 '1' m in
let m = mapInsert 2 '2' m in
let m = mapInsert 3 '3' m in
let m = mapInsert 4 '4' m in
let m = mapInsert 4 '5' m in

utest mapFind 1 m with '1' in
utest mapFind 2 m with '2' in
utest mapFind 3 m with '3' in
utest mapFind 4 m with '5' in

utest mapMem 1 m with true in
utest mapMem 42 m with false in

utest mapAny (lam k. lam v. eqi 1 k) m with true in
utest mapAny (lam k. lam v. eqi (char2int '5') (char2int v)) m with true in
utest mapAny (lam k. lam v. eqi (char2int '4') (char2int v)) m with false in

utest mapBindings m with [(1,'1'), (2,'2'), (3,'3'), (4,'5')] in

let bindsSort = sort (lam t1. lam t2. subi t1.0 t2.0) in

let m = mapMap (lam c. int2char (addi 1 (char2int c))) m in
utest bindsSort (mapBindings m) with [(1,'2'), (2,'3'), (3,'4'), (4,'6')] in

let m = mapMapWithKey (lam k. lam v. int2char (addi k (char2int v))) m in
utest bindsSort (mapBindings m) with [(1,'3'), (2,'5'), (3,'7'), (4,':')] in

-- Int tuple map
let cmpTuple = lam t1. lam t2.
  let d = subi t1.0 t2.0 in
  match d with 0 then
    subi t1.1 t2.1
  else d
in

let m = mapEmpty cmpTuple in

let m = mapInsert (1, 1) 1 m in
let m = mapInsert (1, 1) 2 m in
let m = mapInsert (1, 2) 2 m in
let m = mapInsert (2, 42) 3 m in
let m = mapInsert (3, 42) 4 m in

utest mapFind (1, 1) m with 2 in
utest mapFind (1, 2) m with 2 in
utest mapFind (2, 42) m with 3 in
utest mapFind (3, 42) m with 4 in

()
