include "seq.mc"
include "common.mc"

-- Generalized Levenshtein distance implemented using dynamic programming

-- 'costSub e1 e2' is the cost of a substitution operation

-- 'costDel' is the cost of having to do an insertion operation in order to
-- transform 's2' into 's1'

-- 'costIns' is the cost of having to insert something into 's1'
let levenshteinCost =
  lam costSub : a -> a -> Int.
  lam costDel : Int.
  lam costIns : Int.
  lam eq : a -> a -> Bool.
  lam s1 : [a].
  lam s2 : [a].
    let n1 = addi (length s1) 1 in
    let n2 = addi (length s2) 1 in
    let mat = ref (create n1 (lam i. create n2 (lam i. 0))) in
    recursive let work = lam row. lam col.
      let val =
        if eqi row 0 then
          muli costIns col
        else if eqi col 0 then
          muli costDel row
        else
          let replace =
            let v = get (get (deref mat) (subi row 1)) (subi col 1) in
            let x = get s1 (subi row 1) in
            let y = get s2 (subi col 1) in
            if eq x y then v else addi v (costSub x y)
          in
          let insert = addi (get (get (deref mat) (subi row 1)) col) costIns in
          let delete = addi (get (get (deref mat) row) (subi col 1)) costDel in
          minOrElse (lam. error "Empty sequence") subi
                    [replace, insert, delete]
      in
      modref mat (set (deref mat) row (set (get (deref mat) row) col val));
      if and (eqi row (subi n1 1)) (eqi col (subi n2 1)) then
        ()
      else if eqi col (subi n2 1) then
        work (addi row 1) 0
      else
        work row (addi col 1)
    in
    work 0 0;
    let res =
    get (get (deref mat) (length s1)) (length s2)
    in
    printLn ">>>>> levenshtein";
    dprintLn s1;
    dprintLn s2;
    print "res = "; dprintLn res;
    res

-- Standard Levenshtein distance
let levenshtein = levenshteinCost (lam. lam. 1) 1 1

utest levenshtein eqc "" "" with 0
utest levenshtein eqc "massa" "maska" with 1
utest levenshtein eqc "kitten" "sitting" with 3
utest levenshtein eqc "ACGT" "GCT" with 2

utest levenshtein eqi [1,2,3] [1,3] with 1

utest levenshteinCost (lam. lam. 3) 5 7 eqi [1,2,3] [1,2,3] with 0
-- Substitution cost
utest levenshteinCost (lam. lam. 3) 5 7 eqi [1,2,3] [1,4,3] with 3
-- Deletion cost
utest levenshteinCost (lam. lam. 3) 5 7 eqi [1,2,3] [1,2,3,3] with 5
-- Insertion cost
utest levenshteinCost (lam. lam. 3) 5 7 eqi [1,2,3] [1,3] with 7

