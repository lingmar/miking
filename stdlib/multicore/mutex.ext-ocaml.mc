include "map.mc"
include "ocaml/ast.mc"

let tymutex_ = lam. tyunknown_


let mutexExtMap =
  use OCamlTypeAst in
  mapFromSeq cmpString
  [ ("externalMutexCreate", [
    { ident = "Mutex.create"
    , ty = tyarrow_ otyunit_ tymutex_
    , libraries = []
    }]),

    ("externalMutexLock", [
    { ident = "Mutex.lock"
    , ty = tyarrow_ tymutex_ otyunit_
    , libraries = []
    }]),

    ("externalMutexRelease", [
    { ident = "Mutex.unlock"
    , ty = tyarrow_ tymutex_ otyunit_
    , libraries = []
    }]),

    ("externalMutexTryLock", [
    { ident = "Mutex.try_lock"
    , ty = tyarrow_ tymutex_ tybool_
    , libraries = []
    }])
  ]
