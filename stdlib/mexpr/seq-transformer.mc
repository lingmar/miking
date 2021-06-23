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

-- TODO: don't recurse in utest?
lang SeqTransformer = SeqAst + VarAst + AppAst + UnknownTypeAst
  sem seqTransform =
  | t ->
    let name =
      match findName "create" t with Some name then name
      else nameSym "createUnknown"
    in _seqTransform name t

  sem _seqTransform (create : Name) =
  | TmSeq {tms = tms, info = info} ->
    TmApp
      { lhs = TmApp { lhs = TmVar {ident = create, ty = tyunknown_, info = info}
                    , rhs = int_ (length tms)
                    , ty = tyunknown_
                    , info = info
                    }
      , rhs =
        let i = nameSym "i" in
        nulam_ i (get_ (seq_ (map (_seqTransform create) tms)) (nvar_ i))
      , ty = tyunknown_
      , info = info
      }
  | t -> smap_Expr_Expr (_seqTransform create) t
end

lang TestLang = MExprAst + SeqTransformer + MExprPrettyPrint

mexpr

use TestLang in

let ast = seq_ [int_ 1, int_ 2, int_ 3] in

let ast = seqTransform ast in

printLn (expr2str ast);

()
