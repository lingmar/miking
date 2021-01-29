include "mexpr.mc"
include "pprint.mc"
include "digraph.mc"
include "string.mc"
include "ast-builder.mc"
include "eq-paths.mc"
include "anf.mc"
include "name.mc"
include "hashmap.mc"

-- This file contains implementations related to decision points. In particular,
-- it implements:
-- * A language fragment for decision points (HoleAst)
-- * An algorithm for AST -> call graph conversion (Ast2CallGraph fragment)
-- * Program transformations for programs with decision points (HolyCallGraph)

let _top = nameSym "top"

let _projName = nameSym "x"
let _head = lam s. get_ s (int_ 0)
let _tail = lam s. ntupleproj_ _projName 1 (splitat_ s (int_ 1))
let _null = lam s. eqi_ (int_ 0) (length_ s)

let _drecordproj = use MExprAst in
  lam key. lam r.
  nrecordproj_ _projName key r

let _eqn = lam n1. lam n2.
  if and (nameHasSym n1) (nameHasSym n2) then
    nameEqSym n1 n2
  else
    error "Name without symbol."

let _getSym = lam n.
  (optionGetOrElse
    (lam _. error "Expected symbol")
    (nameGetSym n))

let _nameHash = lam n.
  match nameGetSym n with Some s then sym2hash s
  else hashmapStrTraits (nameGetStr n)

lang HoleAst
  syn Expr =
  | TmHole {startGuess : Expr,
            depth : Int}

  sem symbolizeExpr (env : SymEnv) =
  | TmHole h -> TmHole h

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmHole h -> TmHole h

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmHole h -> acc
end

lang HolePrettyPrint = HoleAst + TypePrettyPrint
  sem isAtomic =
  | TmHole _ -> false

  sem pprintCode (indent : Int) (env : SymEnv) =
  | TmHole h ->
    match pprintCode indent env h.startGuess with (env1, startStr) then
      match pprintCode indent env1 h.depth with (env2, depthStr) then
        (env2,
           join ["Hole (", strJoin ", " [startStr, depthStr],")"])
      else never
    else never
end

lang HoleANF = HoleAst + ANF
  sem isValue =
  | TmHole _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmHole {startGuess = startGuess, depth = depth} ->
    k (TmHole {startGuess = normalizeTerm startGuess, depth = depth})
end

let hole_ = use HoleAst in
  lam startGuess. lam depth.
  TmHole {startGuess = startGuess, depth = depth}

-- Create a call graph from an AST.
-- * Vertices (identifier names) are functions f defined as: let f = lam. ...
-- * There is an edge between f1 and f2 iff f1 calls f2: let f1 = lam. ... (f2 a)
-- * "top" is the top of the graph (i.e., no incoming edges)

type CallGraph = DiGraph Name Symbol

let _handleLetVertex = use FunAst in
  lam letexpr. lam f.
    match letexpr.body with TmLam lm
    then cons letexpr.ident (f lm.body)
    else f letexpr.body

let _handleLetEdge = use FunAst in
  lam letexpr. lam f. lam g. lam prev.
    match letexpr.body with TmLam lm
    then f g letexpr.ident lm.body
    else f g prev letexpr.body

let _handleApps = use AppAst in use VarAst in
  lam id. lam f. lam prev. lam g. lam app.
    recursive let appHelper = lam g. lam app.
      match app with TmApp {lhs = TmVar v, rhs = rhs} then
        let resLhs =
          if digraphHasVertex v.ident g then
            digraphAddEdge prev v.ident id g
          else g
        in f resLhs prev rhs
      else match app with TmApp ({lhs = TmApp a, rhs = rhs}) then
        let resLhs = appHelper g (TmApp a) in
        f resLhs prev rhs
      else match app with TmApp a then
        f (f g prev a.lhs) prev a.rhs
      else never
  in appHelper g app

-- Complexity (I think): O(|V|*|F|), as we visit each node exactly once and each
-- time potentially perform a graph union operation, which we assume has
-- complexity O(|F|). V is the set of nodes in the AST and F is the set of nodes
-- in the call graph (i.e. set of functions in the AST).
lang Ast2CallGraph = LetAst + FunAst + RecLetsAst
  sem toCallGraph =
  | arg ->
    let gempty = digraphAddVertex _top (digraphEmpty _eqn eqsym) in
    let g = digraphAddVertices (_findVertices arg) gempty in
    _findEdges g _top arg

  sem _findVertices =
  | TmLet t ->
    let res_body = _handleLetVertex t _findVertices
    in concat res_body (_findVertices t.inexpr)

  | TmRecLets t ->
    let res =
      foldl (lam a. lam b. concat a (_handleLetVertex b _findVertices))
            [] t.bindings
    in concat res (_findVertices t.inexpr)

  | tm ->
    sfold_Expr_Expr concat [] (smap_Expr_Expr _findVertices tm)

  sem _findEdges (cg : CallGraph) (prev : Name) =
  | TmLet ({body = TmApp a} & t) ->
    let id = _getSym t.ident in
    let resBody = _handleApps id _findEdges prev cg t.body in
    _findEdges resBody prev t.inexpr

  | TmLet ({body = TmLam lm} & t) ->
    let resBody = _findEdges cg t.ident lm.body in
    _findEdges resBody prev t.inexpr

  | TmRecLets t ->
    let res =
      foldl (lam g. lam b. digraphUnion g (_handleLetEdge b _findEdges g prev))
            cg t.bindings
    in _findEdges res prev t.inexpr

  | tm ->
    sfold_Expr_Expr digraphUnion cg (smap_Expr_Expr (_findEdges cg prev) tm)
end

-- Type of a function for looking up decision points assignments
type Lookup v = Symbol -> [Symbol] -> v
type Skeleton v = Lookup v -> Expr

-- The initial value of an incoming variable
let _incomingUndef = gensym ()

-- Get the leftmost node (callee function) in a (nested) application node.
-- Returns an optional: either the name of the variable if the leftmost node is
-- a node, otherwise None ().
let _nestedAppGetCallee = use AppAst in use VarAst in lam tm.
  recursive let work = lam app.
    match app with TmApp {lhs = TmVar v, rhs = rhs} then
      Some v.ident
    else match app with TmApp {lhs = TmApp a} then
        work (TmApp a)
    else None ()
  in work tm

--
lang ContextAwareHoles = Ast2CallGraph + HoleAst + IntAst + SymbAst
  -- Find the initial mapping from decision points to values
  -- Returns a function of type 'Lookup v'.
  sem initAssignments =
  | tm ->
    -- Find the start guess of each decision point
    recursive let findHoles : [(Symbol, a)] -> Expr -> [(Symbol, a)] =
      lam acc. lam t.
        match t with TmLet ({body = TmHole {startGuess = startGuess}} & le) then
          let id = _getSym le.ident in
          findHoles (cons (id, startGuess) acc) le.inexpr
        else
          sfold_Expr_Expr concat acc (smap_Expr_Expr (findHoles acc) t)
    in
    -- Build a hash map for symbol -> value
    let m =
      foldl (lam acc. lam t.
               hashmapInsert {eq = eqsym, hashfn = sym2hash} t.0 t.1 acc)
            hashmapEmpty
            (findHoles [] tm) in
    -- Return a lookup function (path is ignored for initial assignment)
    lam id. lam _path.
      optionGetOrElse
        (lam _. error "Lookup failed")
        (hashmapLookup {eq = eqsym, hashfn = sym2hash} id m)

  -- Assign decision points in a skeleton program.
  -- Returns an MExpr program where decision points have been assigned
  -- values given by the lookup function.
  sem assign ( p : Lookup v ) =
  | skel -> []

  -- Transform a program with decision points.
  -- Returns a function of type 'Skeleton v'. Applying this function to a lookup
  -- function yields an MExpr program where the values of the decision points
  -- have been replaced by values given by the lookup function.
  sem transform (publicFns : [Name]) =
  | tm ->
    -- Compute the call graph
    let cg = toCallGraph tm in

    -- Map node in call graph (name) -> incoming variable name
    -- This information is needed when tracing the execution path.
    let fun2inc =
      foldl (lam acc. lam funName.
               let incVarName = nameSym (concat "inc" (nameGetStr funName)) in
               hashmapInsert {eq = nameEq, hashfn = _nameHash}
                             funName incVarName acc)
            hashmapEmpty
            (digraphVertices cg)
    in
    -- Map edge label in call graph (symbol) -> incoming variable name for its from-node
    -- This information is needed when tracing the execution path.
    -- OPT(Linnea, 2021-01-29): Use relevant labels only (those present in eqPaths)
    let lbl2inc =
      foldl (lam acc. lam edge.
               match edge with (fromVtx, _, lbl) then
                 let incVarName =
                   hashmapLookup {eq = nameEq, hashfn = _nameHash}
                                 fromVtx fun2inc
                 in hashmapInsert {eq = nameEq, hashfn = _nameHash}
                                  lbl incVarName
               else never)
            hashmapEmpty
            (digraphEdges cg)
    in

    -- Declare the incoming variables
    let incVars =
      bindall_ (map (lam incVarName. nulet_ incVarName (ref_ (symb_ _incomingUndef)))
                    (hashmapValues {eq = nameEq, hashfn = _nameHash} fun2inc))
    in
    -- Introduce the incoming variables as global variables
    let tm = bind_ incVars tm in
    -- Make sure caller updates the incoming variable for its callee
    let tm = _updateIncVars fun2inc _top tm in

    -- Replace each decision point with appropriate match statements, given the equivalence paths

    tm

    -- TODO: separate function to introduce global variables, this function just updates caller/callee thing
    sem _updateIncVars (fun2inc : Hashmap Name Name) (cur : Name) =
    -- Application: caller updates incoming variable of callee
    | TmLet ({ body = TmApp a } & t) ->
      -- NOTE(Linnea, 2021-01-29): ANF form means no recursion necessary for the
      -- body of this let expression (cannot contain function definitions or
      -- calls)
      let le = TmLet {t with inexpr = _updateIncVars fun2inc cur t.inexpr} in
      match _nestedAppGetCallee (TmApp a) with Some callee then
        match hashmapLookup {eq = nameEq, hashfn = _nameHash} callee fun2inc
        with Some iv then
          -- Set the incoming var of callee to current node
          let _ = printLn (join ["Calling ", nameGetStr callee, " from ", nameGetStr cur]) in
          let update = modref_ (nvar_ iv) (symb_ (_getSym cur)) in
          bind_
            (nulet_ (nameSym "_") update) le
        else le
      else le
    -- Function definition: possibly update cur inside body of function
    | TmLet ({ body = TmLam lm } & t) ->
      let curBody =
        match hashmapLookup {eq = nameEq, hashfn = _nameHash} t.ident fun2inc
        with Some _ then
          t.ident
        else cur
     in TmLet {{t with body = _updateIncVars fun2inc curBody t.body}
                with inexpr = _updateIncVars fun2inc cur t.inexpr}

    | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
      let newBinds =
        map (lam bind.
               let curBody =
                 match hashmapLookup {eq = nameEq, hashfn = _nameHash}
                                     bind.ident fun2inc
                 with Some _ then bind.ident
                 else cur
               in {bind with body = _updateIncVars fun2inc curBody bind.body})
        bindings
      in TmRecLets {{t with bindings = newBinds}
                     with inexpr = _updateIncVars fun2inc cur inexpr}

    | tm ->
      smap_Expr_Expr (_updateIncVars fun2inc cur) tm
end

lang PPrintLang = MExprPrettyPrint + HolePrettyPrint

lang TestLang = MExpr + ContextAwareHoles + PPrintLang + MExprANF + HoleANF

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

let s1 = gensym () in
let x = nameSetSym (nameNoSym "x") s1 in
let s2 = gensym () in
let y = nameSetSym (nameNoSym "y") s2 in


let ast = anf (ulet_ "f" (bindall_ [ulet_ "x" (ulam_ "x" (nulet_ x (hole_ true_ (int_ 2)))),
                                    ulet_ "y" (ulam_ "y" (nulet_ y (hole_ false_ (int_ 1)))),
                                    app_ (var_ "x") (int_ 1)] )) in

let _ = print (expr2str ast) in

let cg = toCallGraph ast in
-- let _ = dprint (digraphVertices cg) in

let _ = printLn "\n-- Lookups --" in
let lookup = initAssignments ast in
let _ = dprint (lookup s1 []) in
let _ = dprint (lookup s2 []) in
let _ = printLn "\n" in

let _ = printLn "\n-- Transform -- \n" in
let ast = transform [] ast in
let _ = print (expr2str ast) in
--let _ = dprint ast in

let ast = bind_
    (ureclets_add "even" (ulam_ "x" (if_ (eqi_ (var_ "x") (int_ 0))
                                       (true_)
                                       (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
    (ureclets_add "odd" (ulam_ "x" (if_ (eqi_ (var_ "x") (int_ 1))
                                      (true_)
                                      (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
     reclets_empty))
    (app_ (var_ "even") (int_ 2))
in
let ast = anf ast in

let ast = transform [] ast in
let _ = printLn (expr2str ast) in

()
