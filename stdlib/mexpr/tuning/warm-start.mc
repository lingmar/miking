include "string.mc"
include "seq.mc"
include "levenshtein.mc"
include "math.mc"
include "decision-points.mc"
include "mexpr/info.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/type-annot.mc"

recursive let cmpLex : [a -> a -> Int] -> a -> a -> Int =
  lam cmp. lam a. lam b.
    match cmp with [] then 0
    else match cmp with [c] ++ cmp then
      let diff = c a b in
      if eqi 0 diff then
        cmpLex cmp a b
      else diff
    else never
end

utest cmpLex [subi] 1 0 with 1
utest cmpLex [subi, lam. lam. 4] 0 0 with 4

type GlobalInfo = (String, Info, String, Info)

let globalCmp = cmpLex
[ lam g1 : GlobalInfo. lam g2 : GlobalInfo. cmpString g1.0 g2.0
, lam g1 : GlobalInfo. lam g2 : GlobalInfo. infoCmp g1.1 g2.1
, lam g1 : GlobalInfo. lam g2 : GlobalInfo. cmpString g1.2 g2.2
, lam g1 : GlobalInfo. lam g2 : GlobalInfo. infoCmp g1.3 g2.3
]

type PathInfo = (String, Info)

let pathInfoCmp = cmpLex
[ lam p1 : PathInfo. lam p2 : PathInfo.
   cmpString p1.0 p2.0
, lam p1 : PathInfo. lam p2 : PathInfo. infoCmp p1.1 p2.1
]

type HoleInfo =
{ globals : Map GlobalInfo Type
, expansions : Map GlobalInfo (Map [PathInfo] Expr)
}

let holeInfoEmpty =
{ globals = mapEmpty globalCmp
, expansions = mapEmpty globalCmp
}

let indexStr = "index"
let valueStr = "value"
let holeNameStr = "hole_name"
let holeInfoStr = "hole_info"
let funNameStr = "function_name"
let funInfoStr = "function_info"
let pathNameStr = "call_path_functions"
let pathInfoStr = "call_path_infos"

let _startsWith = lam prefix. lam str.
  isPrefix eqc prefix str

let parseString = lam str.
  use BootParser in
  use SeqAst in
  use CharAst in
  match parseMExprString [] str with TmSeq {tms = tms} then
    map (lam x. match x with TmConst {val = CChar {val = c}}
         then c
         else error "impossible") tms
  else error (concat "Not a string: " str)

utest parseString "\"hello\"" with "hello"

let parseInfo = lam str.
  let info = str2info (parseString str) in
  match info with NoInfo () then info
  else match info with Info i then
    Info {i with filename = parseString i.filename}
  else never

let parseHoleInfo : String -> HoleInfo = lam str.
  recursive let createMap = lam acc. lam rows.
    match rows with [] then acc
    else match rows with [r] ++ rows then
      match strIndex '=' r with Some i then
        match splitAt r i with (key, value) then
          createMap
            (mapInsert (strTrim key) (strTrim (tail value)) acc)
            rows
        else never
      else error (concat "Unknown entry in tune file: " r)
    else never
  in

  let entries = tail (strSplit "[[hole]]" (strTrim str)) in
  recursive let work : HoleInfo -> [String] -> HoleInfo =
    lam acc. lam xs.
      match xs with [] then acc
      else match xs with [str] ++ xs then
        let keyVals =
          createMap (mapEmpty cmpString) (strSplit "\n" (strTrim str)) in

        let holeName = parseString (mapFindWithExn holeNameStr keyVals) in
        let holeInfo = parseInfo (mapFindWithExn holeInfoStr keyVals) in
        let funName = parseString (mapFindWithExn funNameStr keyVals) in
        let funInfo = parseInfo (mapFindWithExn funInfoStr keyVals) in

        let expr =
          use BootParser in
          parseMExprString [] (mapFindWithExn valueStr keyVals)
        in
        let ty =
          use MExprTypeAnnot in
          ty (typeAnnot expr)
        in

        let pathNames : [String] =
          let str = parseString (mapFindWithExn pathNameStr keyVals) in
          match str with "" then []
          else map strTrim (strSplit "->" str)
        in
        let pathInfos : [Info] =
          let str = parseString (mapFindWithExn pathInfoStr keyVals) in
          match str with "" then []
          else map str2info (strSplit "->" str)
        in
        let pathInfos : [PathInfo] =
          zipWith (lam s : String. lam i : Info. (s, i))
            pathNames pathInfos
        in

        let insertExpansion =
          lam m : Map [PathInfo] Expr.
          lam global : GlobalInfo.
          lam path : [PathInfo].
          lam expr : Expr.
            let pathMap =
              match mapLookup global m with Some pathMap then
                mapInsert path expr pathMap
              else
                mapInsert path expr (mapEmpty (seqCmp pathInfoCmp))
            in mapInsert global pathMap m
        in

        let global : GlobalInfo = (holeName, holeInfo, funName, funInfo) in
        work
          {{acc with globals = mapInsert global ty acc.globals}
                with expansions = insertExpansion acc.expansions global pathInfos expr}
          xs
      else never
  in work holeInfoEmpty entries

let env2holeInfo : CallCtxEnv -> HoleInfo = lam env.
  match env with { hole2idx = hole2idx, hole2fun = hole2fun, hole2ty = hole2ty } then
    let hole2idx = deref hole2idx in
    let hole2fun = deref hole2fun in
    let hole2ty = deref hole2ty in
    foldl (lam acc : HoleInfo. lam bind : (NameInfo, Map [NameInfo] Int).
      let holeName : String = nameInfoGetStr bind.0 in
      let holeInfo : Info = nameInfoGetInfo bind.0 in
      let funNameInfo : NameInfo = mapFindWithExn bind.0 hole2fun in
      let funName : String = nameInfoGetStr funNameInfo in
      let funInfo : Info = nameInfoGetInfo funNameInfo in
      let globalInfo : GlobalInfo = (holeName, holeInfo, funName, funInfo) in
      let expansions =
        foldl (lam acc. lam paths : [NameInfo].
          match unzip paths with (funNames, funInfos) then
            let funNames : [String] = map nameGetStr funNames in
            let path : [PathInfo] = zipWith (lam n. lam i. (n, i)) funNames funInfos in
            -- Store the index of the hole to build flat lookup table later
            let i = mapFindWithExn paths bind.1 in
            mapInsert path (int_ i) acc
          else never)
          (mapEmpty (seqCmp pathInfoCmp)) (mapKeys bind.1)
      in
      let globals = mapInsert globalInfo (mapFindWithExn bind.0 hole2ty) acc.globals in
      let expansions = mapInsert globalInfo expansions acc.expansions in
      {{acc with globals = globals}
            with expansions = expansions})
    holeInfoEmpty (mapBindings hole2idx)
  else never

-- TODO: types
type DistParams =
{ wHoleName : Float
, wHoleInfo : Float
, wFunName : Float
, wFunInfo : Float
, wInfoFileName : Float
, wInfoRow : Float
, wInfoCol : Float
, pInfoOneNoInfo : Float
, pInfoTwoNoInfo : Float
, pGlobalDistThreshold : Float
, pContextDistThreshold : Float
}

let distParams =
{ wHoleName = 1.0
, wHoleInfo = 1.0
, wFunName = 1.0
, wFunInfo = 1.0
, wInfoFileName = 1.0
, wInfoRow = 1.0
, wInfoCol = 1.0
, pInfoOneNoInfo = inf
, pInfoTwoNoInfo = 0.0
, pGlobalDistThreshold = 10.0
, pContextDistThreshold = 10.0
}

let strDist : String -> String -> Float = lam s1. lam s2.
  int2float (levenshtein s1 s2)

let infoDist = lam i1 : Info. lam i2 : Info.
  let p = distParams in
  match (i1, i2) with (NoInfo _, NoInfo _) then
    p.pInfoTwoNoInfo
  else match i1 with NoInfo _ then
    p.pInfoOneNoInfo
  else match (i1, i2) with (Info i1, Info i2) then
    foldl addf 0.0
    [ mulf p.wInfoFileName (strDist i1.filename i2.filename)
    , mulf p.wInfoRow (int2float (absi (subi i1.row1 i2.row1)))
    , mulf p.wInfoCol (int2float (absi (subi i1.col1 i2.col1)))
    ]
  else never

let globalDist = lam x1 : (GlobalInfo, Type). lam x2 : (GlobalInfo, Type).
  use MExprEq in
  let g1 = x1.0 in
  let g2 = x2.0 in
  let p = distParams in
  -- print "Comparing "; print g1.0; print " "; printLn g2.0;
  -- dprintLn g1;
  -- dprintLn g2;
  let res =
    if eqType [] x1.1 x2.1 then
      foldl addf 0.0
      [ mulf p.wHoleName (strDist g1.0 g2.0)
      , mulf p.wHoleInfo (infoDist g1.1 g2.1)
      , mulf p.wFunName  (strDist g1.2 g2.2)
      , mulf p.wFunInfo  (infoDist g1.3 g2.3)
      ]
    else inf
  in
  -- print "distance "; dprintLn res;
  res

utest
  globalDist
    (("x", NoInfo (), "y", NoInfo ()), tyunknown_)
    (("x", NoInfo (), "y", NoInfo ()), tyunknown_)
with 0.0 using eqfApprox 1e-15

utest
  globalDist
    (("x", NoInfo (), "y", NoInfo ()), tyint_)
    (("x", NoInfo (), "y", NoInfo ()), tybool_)
with inf using eqf

let contextDist = lam. lam. 0.0

let cmpf = lam f1. lam f2.
  let diff = subf f1 f2 in
  if ltf 0.0 diff then floorfi diff
  else if eqfApprox 1e-15 0.0 diff then 0
  else ceilfi diff

utest min cmpf [0.0, subf 0.0 0.0001, 290.0] with Some (subf 0.0 0.0001)
using optionEq (eqfApprox 1e-15)

let _parseInt : Expr -> Int = use IntAst in
  lam t.
    match t with TmConst {val = CInt {val = i}} then i
    else dprintLn t; error "impossible"

let tryMatchHoles = lam tuneFile : String. lam env : CallCtxEnv.
  let params = distParams in
  let str = readFile tuneFile in

  match strIndex '[' (readFile tuneFile) with Some i then
    match splitAt str i with (_, suffix) then
      fprintLn "before";

      -- Compute the old and new hole info structs
      let oldHoleInfo = parseHoleInfo suffix in
      let newHoleInfo = env2holeInfo env in

      -- Find the best globally matched old hole for each new hole
      let bestMatchGlobals : Map GlobalInfo (Float, GlobalInfo) =
        foldl (lam acc : Map GlobalInfo GlobalInfo. lam new : (GlobalInfo, Type).
          let dists : [(Float, GlobalInfo)] =
            map (lam old : (GlobalInfo, Type). (globalDist new old, old.0))
              (mapBindings oldHoleInfo.globals)
          in
          let bestMatch : Option (Float, GlobalInfo) =
            min (lam t1 : (Float, GlobalInfo). lam t2 : (Float, GlobalInfo).
              cmpf t1.0 t2.0) dists
          in
          match bestMatch with Some bestMatch then
            let bestMatch : (Float, GlobalInfo) = bestMatch in
            let bestDist = bestMatch.0 in
            if leqf bestDist params.pGlobalDistThreshold then
              mapInsert new.0 bestMatch acc
            else acc
          else acc)
        (mapEmpty globalCmp)
        (mapBindings newHoleInfo.globals)
      in

      printLn "***";
      dprintLn (mapBindings bestMatchGlobals);

      -- Compute best context expanded matches for the global matches
      let bestMatchExpanded
        : Map GlobalInfo
            (Map [PathInfo] (Float (GlobalInfo, [PathInfo]))) =
        foldl (lam acc : Map GlobalInfo (Map [PathInfo] (GlobalInfo, [PathInfo])).
               lam new : (GlobalInfo, Map [PathInfo] Expr).
          let matchMap : Map [PathInfo] (GlobalInfo, [PathInfo]) =
            foldl
            (lam acc : Map [PathInfo] (GlobalInfo, [PathInfo]).
             lam newPath : [PathInfo].
               let dists : [(Float, (GlobalInfo, [PathInfo]))] =
                 let bestGlobal = mapLookup new.0 bestMatchGlobals in
                 match bestGlobal with Some (globalDist, globalInfo) then
                   let oldPaths =
                     mapKeys (mapFindWithExn globalInfo oldHoleInfo.expansions)
                   in
                   map (lam oldPath : [PathInfo].
                          (contextDist newPath oldPath, (globalInfo, oldPath)))
                       oldPaths
                 else match bestGlobal with None () then []
                 else never
               in
               let bestMatch : Option (Float, (Globalinfo, [PathInfo])) =
                 min (lam t1 : (Float, (GlobalInfo, [PathInfo])).
                      lam t2 : (Float, (GlobalInfo, [PathInfo])).
                   cmpf t1.0 t2.0
                 ) dists in
               match bestMatch with Some bestMatch then
                 let bestMatch : (Float, (GlobalInfo, [PathInfo])) = bestMatch in
                 let bestDist = bestMatch.0 in
                 if leqf bestDist params.pContextDistThreshold then
                   mapInsert newPath bestMatch acc
                 else acc
               else acc)
            (mapEmpty (seqCmp pathInfoCmp))
            (mapKeys new.1)
          in mapInsert new.0 matchMap acc)
          (mapEmpty globalCmp)
          (mapBindings newHoleInfo.expansions)
      in

      printLn "*** Context expanded ***";
      dprintLn (mapBindings bestMatchExpanded);
      mapMapWithKey (lam k. lam v.
        print "global: "; dprintLn k;
        dprintLn (mapBindings v))
        bestMatchExpanded;

      -- Compute a lookup table from the match
      let tableMap =
        let idx2hole = deref env.idx2hole in
        foldl (lam acc : Map Int Expr.
               lam bind : (GlobalInfo, Map [PathInfo] Expr).
          let newGlobal = bind.0 in
          let contextMap
            : Option (Map [PathInfo] (Float, (GlobalInfo, [PathInfo]))) =
            mapLookup newGlobal bestMatchExpanded
          in

          foldl (lam acc : Map Int Expr. lam bind : ([PathInfo], Expr).
            let path = bind.0 in
            let i = _parseInt bind.1 in
            dprintLn i;
            let defaultVal = lam.
              use HoleAst in
              default (get idx2hole i)
            in
            let val =
              match contextMap with Some contextMap then
                match mapLookup path contextMap
                with Some (dist, (matchGlobal, matchContext)) then
                  fdprintLn (mapLookup path contextMap);
                  let m = mapFindWithExn matchGlobal oldHoleInfo.expansions in
                  fprintLn "*** here ***";
                  mapFindWithExn matchContext
                    (mapFindWithExn matchGlobal oldHoleInfo.expansions)
                else defaultVal () -- No global match
              else defaultVal () -- No context match
            in mapInsert i val acc
            )
            acc
            (mapBindings bind.1)
        )
        (mapEmpty subi)
        (mapBindings newHoleInfo.expansions)

      in
      let table = mapValues tableMap in
      dprintLn (use MExprPrettyPrint in map expr2str table);

      fprintLn "after";
      table
    else error "impossible"
  else error "Cannot read info from tune file"

mexpr
let holeInfo = parseHoleInfo (readFile "warm-start.toml") in

utest map (lam t : GlobalInfo. t.0) (mapKeys holeInfo.globals) with ["h1", "h1", "h2"] in

utest map (lam t : GlobalInfo. t.1) (mapKeys holeInfo.globals) with
[ Info
  { filename = "test/examples/tuning/tune-context.mc"
  , row1 = 22 , row2 = 22
  , col1 = 2 , col2 = 50
  },
  Info
  { filename = "test/examples/tuning/tune-context.mc"
  , row1 = 5, row2 = 5
  , col1 = 2, col2 = 50
  },
  Info
  { filename = "test/examples/tuning/tune-context.mc"
  , row1 = 6, row2 = 6
  , col1 = 2, col2 = 50
  }
]
in

utest map (lam t : GlobalInfo. t.2) (mapKeys holeInfo.globals) with ["bar", "foo", "foo"] in

utest map (lam t : GlobalInfo. t.3) (mapKeys holeInfo.globals) with
[ Info
  { filename = "test/examples/tuning/tune-context.mc"
  , row1 = 21 , row2 = 21
  , col1 = 0, col2 = 9
  },
  Info
  { filename = "test/examples/tuning/tune-context.mc"
  , row1 = 4, row2 = 4
  , col1 = 0, col2 = 9
  },
  Info
  { filename = "test/examples/tuning/tune-context.mc"
  , row1 = 4, row2 = 4
  , col1 = 0, col2 = 9
  }
]
in

--dprintLn (mapValues holeInfo.expansions);

--dprintLn (map mapBindings (mapValues holeInfo.expansions));

()
