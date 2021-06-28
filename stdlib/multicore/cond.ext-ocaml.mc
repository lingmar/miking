include "map.mc"
include "ocaml/ast.mc"
include "mutex.ext-ocaml.mc"

let tycond_ = lam. tyunknown_


let condExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalCondCreate", [
    { ident = "Condition.create"
    , ty = tyarrow_ otyunit_ tycond_
    , libraries = []
    }]),

    ("externalCondWait", [
    { ident = "Condition.wait"
    , ty = tyarrows_ [tycond_, tyunknown_, otyunit_]
    , libraries = []
    }]),

    ("externalCondSignal", [
    { ident = "Condition.signal"
    , ty = tyarrow_ tycond_ otyunit_
    , libraries = []
    }]),

    ("externalCondBroadcast", [
    { ident = "Condition.broadcast"
    , ty = tyarrow_ tycond_ otyunit_
    , libraries = []
    }])
  ]
