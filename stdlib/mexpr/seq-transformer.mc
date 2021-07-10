-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Transforms an MExpr expression where sequence literals (TmSeq) are replaced
-- by a call to create.

include "ast.mc"
include "pprint.mc"
include "ast-builder.mc"
include "common.mc"
include "utesttrans.mc"
include "mexpr/tuning/decision-points.mc"

let seqIndex = ref 0

let _distinct = lam cmp. lam seq.
  setToSeq (setOfSeq cmp seq)

-- sample n elements out of 1..m
let _sample = lam n. lam m.
  randSetSeed 7;
  if gti n m then
    error (join ["cannot sample ", int2string n, " from ", int2string m])
  else
    let mvals = create m (lam i. addi i 1) in
    let nrands = lam n.
      let nvals = create n (lam. ()) in
      map (lam. optionGetOrElse (lam. error "impossible") (randElem mvals)) nvals
    in
    recursive let noRepetition = lam vals.
      let distinctVals = _distinct subi vals in
      let diff = subi (length vals) (length distinctVals) in
      if eqi 0 diff then distinctVals
      else
        noRepetition (concat distinctVals (nrands diff))
    in noRepetition (nrands n)

utest _sample 0 3 with []
utest _sample 1 1 with [1]
-- utest sample 10 100 with [32,38,43,44,45,54,59,61,83,89]

-- TODO: don't recurse in utest?
lang SeqTransformer = MExpr
  sem seqTransform (limit : Int) =
  | t ->
    let nameCreate =
      match findName "create" t with Some name then name
      else nameSym "createUnknown"
    in
    let nameDefault =
      match findName "createDefault" t with Some name then name
      else nameSym "createDefaultUnknown"
    in
    let nbrSeqs = _seqCount t in
    print "nbrSeqs = "; dprint nbrSeqs; flushStdout ();
    let indices = _sample (mini limit nbrSeqs) nbrSeqs in
    print "nbr indices : "; dprint (length indices);
    _seqTransform nameCreate nameDefault indices t

  sem _seqTransform (create : Name) (default : Name) (indices : [Int]) =
  | TmSeq ({tms = tms, info = info} & t) ->
    let curIdx = deref seqIndex in
    modref seqIndex (addi (deref seqIndex) 1);
    match find (eqi curIdx) indices with Some _ then
      TmApp
        { lhs = TmApp { lhs = TmVar {ident = create, ty = tyunknown_, info = info}
                      , rhs = int_ (length tms)
                      , ty = tyunknown_
                      , info = info
                      }
        , rhs =
          let i = nameSym "i" in
          nulam_ i (get_ (seq_ (map (_seqTransform create default indices) tms)) (nvar_ i))
        , ty = tyunknown_
        , info = info
        }
    else
      TmApp
        { lhs = TmApp { lhs = TmVar {ident = default, ty = tyunknown_, info = info}
                      , rhs = int_ (length tms)
                      , ty = tyunknown_
                      , info = info
                      }
        , rhs =
          let i = nameSym "i" in
          nulam_ i (get_ (seq_ (map (_seqTransform create default indices) tms)) (nvar_ i))
        , ty = tyunknown_
        , info = info
        }
      -- TmSeq t
  | t -> smap_Expr_Expr (_seqTransform create default indices) t

  sem _seqCount =
  | TmSeq {tms = tms} ->
    let res = foldl addi 0 (map _seqCount tms) in
    addi 1 res
  | t ->
    sfold_Expr_Expr addi 0 (smap_Expr_Expr _seqCount t)
end

lang TestLang = MExprAst + SeqTransformer + MExprPrettyPrint

mexpr

use TestLang in

let ast = seq_ [int_ 1, int_ 2, int_ 3] in

let count = _seqCount ast in

utest count with 1 in
utest _seqCount (int_ 0) with 0 in
utest _seqCount (bind_ (ulet_ "a" (seq_ [])) (seq_ [int_ 0])) with 2 in

let t = seqTransform 1 ast in
printLn (expr2str t);

let t = seqTransform 1 (bind_ (ulet_ "a" (seq_ [])) (seq_ [int_ 0])) in
printLn (expr2str t);

()
