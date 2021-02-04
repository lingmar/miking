include "mexpr.mc"
include "pprint.mc"
include "digraph.mc"
include "string.mc"
include "ast-builder.mc"
include "eq-paths.mc"
include "anf.mc"
include "name.mc"
include "hashmap.mc"

-- This file contains implementations related to decision points.

-- TODO
-- More test cases
-- Enable debugging of symbols in pprint?
-- Represent paths as trees?
-- Handle public functions: make dummy nodes and match in lookup

let _getSym = lam n.
  optionGetOrElse
    (lam _. error "Expected symbol")
    (nameGetSym n)

let _eqn = lam n1. lam n2.
  if and (nameHasSym n1) (nameHasSym n2) then
    nameEqSym n1 n2
  else
    error "Name without symbol."

let _nameHash = lam n.
  sym2hash (_getSym n)

-------------------------
-- Call graph creation --
-------------------------

-- NOTE(Linnea, 2021-02-03): the call graph creation algorithm assumes that the
-- AST is symbolized and in ANF.

-- The type of the call graph. Vertices are names of function identifiers, edges
-- are names of application nodes.
type CallGraph = DiGraph Name Name

-- The top of the call graph, has no incoming edges.
let _callGraphTop = nameSym "top"

-- Helper functions
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

-- NOTE(Linnea, 2021-02-03): Complexity O(|V|*|F|), as we visit each node
-- exactly once and each time potentially perform a graph union operation, which
-- we assume has complexity O(|F|). V is the set of nodes in the AST and F is
-- the set of nodes in the call graph (i.e. set of functions in the AST).
lang Ast2CallGraph = LetAst + FunAst + RecLetsAst
  sem toCallGraph =
  | arg ->
    let gempty = digraphAddVertex _callGraphTop (digraphEmpty _eqn _eqn) in
    let g = digraphAddVertices (_findVertices arg) gempty in
    _findEdges g _callGraphTop arg

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
    let resBody = _handleApps t.ident _findEdges prev cg t.body in
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

--------------------------------------------
-- Language fragments for decision points --
--------------------------------------------

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
    match pprintCode indent env h.startGuess with (env, startStr) then
      (env,
         join ["hole ", startStr, " ", int2string h.depth])
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

------------------------------
-- Call context information --
------------------------------

-- Maintains call context information necessary for program transformations.
-- This information is static and is thus computed once for each program.
type CallCtxInfo = {

  -- Call graph of the program. Functions are nodes, function calls are edges.
  callGraph: DiGraph Name Name,

  -- Maps names of functions to the name of its incoming variable. The incoming
  -- variables keep track of the execution path during runtime.
  fun2inc: Hashmap Name Name,

  -- Maps edge labels in the call graph to the incoming variable name of its
  -- from-node.
  lbl2inc: Hashmap Name Name,

  -- Each node in the call graph assigns a per-node unique integer to each
  -- incoming edge. This map maps an edge symbol to the count value of its
  -- destination node.
  lbl2count: Hashmap Name Int,

  -- List of public functions in the program.
  publicFns: [Name]

}

-- Compute the call context info from a program.
let callCtxInit : [Name] -> CallGraph Name Name -> Expr -> CallCtxInfo =
  lam publicFns. lam callGraph. lam tm.
    let fun2inc =
      foldl (lam acc. lam funName.
               let incVarName = nameSym (concat "inc_" (nameGetStr funName)) in
               hashmapInsert {eq = _eqn, hashfn = _nameHash}
                 funName incVarName acc)
            hashmapEmpty
            (digraphVertices callGraph)
    in
    let lbl2inc =
      foldl (lam acc. lam edge.
               match edge with (fromVtx, _, lbl) then
                 let incVarName =
                   optionGetOrElse (lam _. error "Internal error: lookup failed")
                     (hashmapLookup {eq = _eqn, hashfn = _nameHash}
                        fromVtx fun2inc)
                 in hashmapInsert {eq = _eqn, hashfn = _nameHash}
                      lbl incVarName acc
               else never)
            hashmapEmpty
            (digraphEdges callGraph)
    in
    let lbl2count =
      foldl (lam acc. lam funName.
               let incomingEdges = digraphEdgesTo funName callGraph in
               match foldl (lam acc. lam e.
                              match e with (_, _, lbl) then
                                match acc with (hm, i) then
                                  (hashmapInsert {eq = _eqn, hashfn = _nameHash}
                                     lbl i hm,
                                   addi i 1)
                                else never
                              else never)
                           (acc, 1)
                           incomingEdges
               with (hm, _) then hm
               else never)
            hashmapEmpty
            (digraphVertices callGraph)
  in
  { callGraph = callGraph, fun2inc = fun2inc, lbl2inc = lbl2inc,
    lbl2count = lbl2count, publicFns = publicFns }

-- Returns the binding of a function name, or None () if the name is not a node
-- in the call graph.
let callCtxFunLookup : Name -> CallCtxInfo -> Option Name = lam name. lam info.
  match info with { fun2inc = fun2inc } then
    hashmapLookup {eq = _eqn, hashfn = _nameHash} name fun2inc
  else never

-- Get the incoming variable name of a function, giving an error if the function
-- name is not part of the call graph.
let callCtxFun2Inc : Name -> CallCtxInfo -> Name = lam name. lam info.
  optionGetOrElse (lam _. error "fun2inc lookup failed")
                  (callCtxFunLookup name info)

-- Get the incoming variable name of an edge label, giving an error if the edge
-- is not part of the call graph.
let callCtxLbl2Inc : Name -> CallCtxInfo -> Name = lam lbl. lam info.
  match info with { lbl2inc = lbl2inc } then
    optionGetOrElse (lam _. error "lbl2inc lookup failed")
                    (hashmapLookup {eq = _eqn, hashfn = _nameHash}
                                   lbl lbl2inc)
  else never

-- Get the count of an edge label, giving an error if the edge is not part of
-- the call graph.
let callCtxLbl2Count : Name -> CallCtxInfo -> Int = lam lbl. lam info.
  match info with { lbl2count = lbl2count } then
    optionGetOrElse (lam _. error "lbl2count lookup failed")
                    (hashmapLookup {eq = _eqn, hashfn = _nameHash}
                                   lbl lbl2count)
  else never

-- Get all the incoming variable names of the program.
let callCtxIncVarNames : CallCtxInfo -> [Name] = lam info.
  match info with { fun2inc = fun2inc } then
    hashmapValues {eq = _eqn, hashfn = _nameHash} fun2inc
  else never

-----------------------------
-- Program transformations --
-----------------------------

-- Type of a function for looking up decision points assignments
-- TODO: What is the best interface for Lookup?
type Lookup = Name -> [Name] -> Expr
type Skeleton = Lookup -> Expr

-- The initial value of an incoming variable
let _incUndef = 0

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

-- Generate skeleton code for looking up a value of a decision point depending
-- on its call history
-- TODO: handle public function
let _lookupCallCtx : Lookup -> Name -> Name -> CallCtxInfo -> [[Name]] -> Skeleton =
  use MatchAst in use NeverAst in
    lam lookup. lam holeId. lam incVarName. lam info. lam paths.
      match info with { lbl2inc = lbl2inc } then
        -- TODO: Represent paths as trees, then this partition becomes trivial
        let partitionPaths : [[Name]] -> ([Name], [[[Name]]]) = lam paths.
          let startVals = foldl (lam acc. lam p.
                                   setInsert _eqn (head p) acc)
                                [] paths in
          let partition = (makeSeq (length startVals) []) in
          let partition =
            mapi
              (lam i. lam _. filter (lam p. _eqn (head p) (get startVals i)) paths)
              partition
          in
          (startVals, partition)
        in
        recursive let work : Name -> [[Name]] -> [Name] -> Expr =
          lam incVarName. lam paths. lam acc.
            let nonEmpty = filter (lam p. not (null p)) paths in
            match partitionPaths nonEmpty with (startVals, partition) then
              let branches =
                mapi (lam i. lam n.
                        let iv = callCtxLbl2Inc n info in
                        let count = callCtxLbl2Count n info in
                        matchex_ (deref_ (nvar_ incVarName)) (pint_ count)
                                 (work iv (map tail (get partition i)) (cons n acc)))
                     startVals
              in
              let defaultVal =
                if eqi (length nonEmpty) (length paths) then never_
                else lookup holeId acc
              in
              matchall_ (snoc branches defaultVal)
            else never
          in
        work incVarName (map reverse paths) []
      else never

--
lang ContextAwareHoles = Ast2CallGraph + HoleAst + IntAst + MatchAst + NeverAst
                         -- Included for debugging
                         + MExprPrettyPrint

  -- Find the initial mapping from decision points to values
  -- Returns a function of type 'Lookup'.
  sem initAssignments =
  | tm ->
    -- Find the start guess of each decision point
    recursive let findHoles : [(Name, Expr)] -> Expr -> [(Name, Expr)] =
      lam acc. lam t.
        match t with TmLet ({body = TmHole {startGuess = startGuess}} & le) then
          findHoles (cons (le.ident, startGuess) acc) le.inexpr
        else
          sfold_Expr_Expr concat acc (smap_Expr_Expr (findHoles acc) t)
    in
    -- Build a hash map for symbol -> value
    let m =
      foldl (lam acc. lam t.
               hashmapInsert {eq = _eqn, hashfn = _nameHash} t.0 t.1 acc)
            hashmapEmpty
            (findHoles [] tm) in
    -- Return a lookup function (path is ignored for initial assignment)
    lam id. lam _path.
      optionGetOrElse
        (lam _. error "Lookup failed")
        (hashmapLookup {eq = _eqn, hashfn = _nameHash} id m)

  -- Transform a program with decision points. Returns a function of type
  -- 'Skeleton'. Applying this function to a lookup function yields an MExpr
  -- program where the values of the decision points have been statically
  -- replaced by values given by the lookup function.
  sem transform (publicFns : [Name]) =
  | tm ->
    let info = callCtxInit publicFns (toCallGraph tm) tm in
    -- Declare the incoming variables
    let incVars =
      bindall_ (map (lam incVarName. nulet_ incVarName (ref_ (int_ _incUndef)))
                    (callCtxIncVarNames info))
    in
    let tm = bind_ incVars tm in
    lam lookup. _maintainCallCtx lookup info _callGraphTop tm

    -- Update incoming variables appropriately for function calls
    sem _maintainCallCtx (lookup : Lookup) (info : CallCtxInfo) (cur : Name) =
    -- Application: caller updates incoming variable of callee
    | TmLet ({ body = TmApp a } & t) ->
      -- NOTE(Linnea, 2021-01-29): ANF form means no recursion necessary for an
      -- application node (cannot contain function definitions or calls)
      -- TODO: Double check above
      let le = TmLet {t with inexpr = _maintainCallCtx lookup info cur t.inexpr} in
      match _nestedAppGetCallee (TmApp a) with Some callee then
        match callCtxFunLookup callee info
        with Some iv then
          -- Set the incoming var of callee to current node
          let count = callCtxLbl2Count t.ident info in
          let update = modref_ (nvar_ iv) (int_ count) in
          bind_
            (nulet_ (nameSym "_") update) le
        else le
      else le

    -- Decision point: lookup the value depending on calling context
    | TmLet ({ body = TmHole { depth = depth }, ident = ident} & t) ->
       match info with
        { callGraph = callGraph, publicFns = publicFns }
       then
         let paths = eqPaths callGraph cur depth publicFns in
         let iv = callCtxFun2Inc cur info in
         let lookupCode = _lookupCallCtx lookup ident iv info paths in
         TmLet {{t with body = lookupCode}
                   with inexpr = _maintainCallCtx lookup info cur t.inexpr}
       else never

    -- Function definitions: possibly update cur inside body of function
    | TmLet ({ body = TmLam lm } & t) ->
      let curBody =
        match callCtxFunLookup t.ident info with Some _
        then t.ident
        else cur
      in TmLet {{t with body = _maintainCallCtx lookup info curBody t.body}
                   with inexpr = _maintainCallCtx lookup info cur t.inexpr}

    | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
      let newBinds =
        map (lam bind.
               match bind with { body = TmLam lm } then
                 let curBody =
                   match callCtxFunLookup bind.ident info with Some _
                   then bind.ident
                   else cur
                 in {bind with body = _maintainCallCtx lookup info curBody bind.body}
               else {bind with body = _maintainCallCtx lookup info cur bind.body})
        bindings
      in TmRecLets {{t with bindings = newBinds}
                       with inexpr = _maintainCallCtx lookup info cur inexpr}
    | tm ->
      smap_Expr_Expr (_maintainCallCtx lookup info cur) tm
end

lang PPrintLang = MExprPrettyPrint + HolePrettyPrint

lang TestLang = MExpr + ContextAwareHoles + PPrintLang + MExprANF + HoleANF

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

let funA = nameSym "funA" in
let funB = nameSym "funB" in
let funC = nameSym "funC" in
let funD = nameSym "funD" in

let pprint = lam ast.
  let _ = printLn "----- BEFORE ANF -----\n" in
  let _ = printLn (expr2str ast) in
  let ast = anf ast in
  let _ = printLn "\n----- AFTER ANF -----\n" in
  let _ = printLn (expr2str ast) in
  let skel = transform [] ast in
  let lookup = initAssignments ast in
  let _ = printLn "\n----- AFTER TRANSFORMATION -----\n" in
  let _ = printLn (expr2str (skel lookup)) in
  (skel lookup)
in

let ast = (bindall_
  [  (nureclets_add funA (ulam_ "x" (bind_ (ulet_ "h" (hole_ true_ 2))
                                  (if_ (var_ "h")
                                       (app_ (nvar_ funB) (addi_ (var_ "x") (int_ 1)))
                                       (app_ (nvar_ funA) (int_ 1)))))
     (nureclets_add funB (ulam_ "x" (if_ (geqi_ (var_ "x") (int_ 5))
                                         (var_ "x")
                                         (app_ (nvar_ funA) (addi_ (var_ "x") (int_ 1)))))
     reclets_empty))
   , nulet_ funC (ulam_ "x" (ulam_ "y" (if_ (var_ "x")
                                            (app_ (nvar_ funA) (int_ 0))
                                            (app_ (nvar_ funA) (var_ "y")))))
   , nulet_ funD (ulam_ "x" (appf2_ (nvar_ funC) (var_ "x") (int_ 2)))
   , ulet_ "a" (appf2_ (nvar_ funC) true_ (int_ 0))
   , ulet_ "b" (appf2_ (nvar_ funC) false_ (int_ 1))
   , ulet_ "c" (app_ (nvar_ funD) true_)
   , ulet_ "d" (app_ (nvar_ funD) false_)
   , tuple_ [(var_ "a"), (var_ "b"), (var_ "c"), (var_ "d")]
  ]) in
-- let prog = pprint ast in
--let res = eval { env = [] } prog in
--let _ = dprint res in

-- let funA = lam _.
--   let h = hole 0 2 in
--   h
-- in
-- let funB = lam x. lam y.
--   if x then
--      (if y then
--         funB z false
--       else funA y)
--   else funA y
-- in
-- let funC = lam x. funB x false
-- in ()
let ast = bindall_ [  nulet_ funA (ulam_ "_"
                        (bind_ (ulet_ "h" (hole_ (int_ 0) 2))
                               (var_ "h")))
                    , nureclets_add funB
                        (ulam_ "x"
                          (ulam_ "y" (if_ (var_ "x")
                                          (if_ (var_ "y")
                                               (appf2_ (nvar_ funB) true_ false_)
                                               (app_ (nvar_ funA) (var_ "x")))
                                          (app_ (nvar_ funA) (var_ "y")))))
                        reclets_empty
                    , nulet_ funC (ulam_ "x"
                        (appf2_ (nvar_ funB) (var_ "x") false_))
                   ]
in
let _ = pprint ast in
let ast = anf ast in
let cg = toCallGraph ast in
let edgeCB =
  match digraphEdgesBetween funC funB cg with [(_,_,sym)]
  then sym else error "Expected one edge"
in
let edgesBA =
  match digraphEdgesBetween funB funA cg with [(_,_,s1), (_,_,s2)]
  then [s1, s2] else error "Expected two edges"
in
let edgeBA1 = head edgesBA in
let edgeBA2 = last edgesBA in
let edgeBB =
  match digraphEdgesBetween funB funB cg with [(_,_,sym)]
  then sym else error "Expected one edge"
in

let eqNameSeq = setEqual _eqn in

let lookup = lam _. lam path.
  match      eqNameSeq path [edgeCB, edgeBA1] with true then int_ 1
  else match eqNameSeq path [edgeCB, edgeBA2] with true then int_ 2
  else match eqNameSeq path [edgeBB, edgeBA1] with true then int_ 3
  else match eqNameSeq path [edgeBB, edgeBA2] with true then int_ 4
  else match eqNameSeq path [edgeBA1]            with true then int_ 5
  else match eqNameSeq path [edgeBA2]            with true then int_ 6
  else error "Unknown path"
in

let appendToAst = lam ast. lam suffix.
  let ast = bind_ ast suffix in
  let skel = transform [funC, funB] ast in
  skel lookup
in

utest eval { env = [] } (appendToAst ast
  (app_ (nvar_ funC) true_)
) with int_ 1 in

utest eval { env = [] } (appendToAst ast
  (app_ (nvar_ funC) false_)
) with int_ 2 in

utest eval { env = [] } (appendToAst ast
  (appf2_ (nvar_ funB) true_ true_)
) with int_ 3 in

utest eval { env = [] } (appendToAst ast
  (appf2_ (nvar_ funB) true_ false_)
) with int_ 5 in

utest eval { env = [] } (appendToAst ast
  (appf2_ (nvar_ funB) false_ false_)
) with int_ 6 in

utest eval { env = [] } (appendToAst ast
  (bind_ (nulet_ (nameSym "_") (app_ (nvar_ funC) false_))
         (appf2_ (nvar_ funB) false_ false_))
) with int_ 6 in

-- let s1 = gensym () in
-- let x = nameSetSym (nameNoSym "x") s1 in
-- let s2 = gensym () in
-- let y = nameSetSym (nameNoSym "y") s2 in


-- let ast = anf (ulet_ "f" (bindall_ [ulet_ "x" (ulam_ "x" (nulet_ x (hole_ true_ 2))),
--                                     ulet_ "y" (ulam_ "y" (nulet_ y (hole_ false_ 1))),
--                                     ulet_ "_" (app_ (var_ "x") (int_ 1)),
--                                     ulet_ "_" (app_ (var_ "x") (int_ 1))] )) in

-- let _ = print (expr2str ast) in

-- let cg = toCallGraph ast in
-- -- let _ = dprint (digraphVertices cg) in

-- let _ = printLn "\n-- Lookups --" in
-- let lookup = initAssignments ast in
-- let _ = dprint (lookup s1 []) in
-- let _ = dprint (lookup s2 []) in
-- let _ = printLn "\n" in

-- let _ = printLn "\n-- Transform -- \n" in
-- let skel = transform [] ast in
-- let _ = print (expr2str (skel lookup)) in
-- --let _ = dprint ast in

-- let ast = bind_
--     (ureclets_add "even" (ulam_ "x" (if_ (eqi_ (var_ "x") (int_ 0))
--                                        (true_)
--                                        (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
--     (ureclets_add "odd" (ulam_ "x" (if_ (eqi_ (var_ "x") (int_ 1))
--                                       (true_)
--                                       (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
--      reclets_empty))
--     (app_ (var_ "even") (int_ 2))
-- in
-- let ast = anf ast in

-- let skel = transform [] ast in
-- let lookup = initAssignments ast in
-- let _ = printLn (expr2str (skel lookup)) in

()
