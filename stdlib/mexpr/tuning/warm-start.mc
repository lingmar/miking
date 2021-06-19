include "string.mc"
include "seq.mc"
include "mexpr/info.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"

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

type HoleType
con IntHole : () -> HoleType
con BoolHole : () -> HoleType
con UnknownHole : () -> HoleType

type HoleInfo =
{ globals : Map GlobalInfo HoleType
, expansions : Map GlobalInfo (Map [PathInfo] Expr)
}

let holeInfoEmpty =
{ globals = mapEmpty globalCmp
, expansions = mapEmpty globalCmp
}

let indexStr = "index"
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

let parseInfo = compose str2info parseString

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

        let ty = UnknownHole () in
        let expr = int_ 0 in

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

mexpr
let holeInfo = parseHoleInfo (readFile "warm-start.toml") in

utest map (lam t : GlobalInfo. t.0) (mapKeys holeInfo.globals) with ["h1", "h1", "h2"] in

utest map (lam t : GlobalInfo. t.1) (mapKeys holeInfo.globals) with
[ Info
  { filename = "\"test/examples/tuning/tune-context.mc\""
  , row1 = 22 , row2 = 22
  , col1 = 2 , col2 = 50
  },
  Info
  { filename = "\"test/examples/tuning/tune-context.mc\""
  , row1 = 5, row2 = 5
  , col1 = 2, col2 = 50
  },
  Info
  { filename = "\"test/examples/tuning/tune-context.mc\""
  , row1 = 6, row2 = 6
  , col1 = 2, col2 = 50
  }
]
in

utest map (lam t : GlobalInfo. t.2) (mapKeys holeInfo.globals) with ["bar", "foo", "foo"] in

utest map (lam t : GlobalInfo. t.3) (mapKeys holeInfo.globals) with
[ Info
  { filename = "\"test/examples/tuning/tune-context.mc\""
  , row1 = 21 , row2 = 21
  , col1 = 0, col2 = 9
  },
  Info
  { filename = "\"test/examples/tuning/tune-context.mc\""
  , row1 = 4, row2 = 4
  , col1 = 0, col2 = 9
  },
  Info
  { filename = "\"test/examples/tuning/tune-context.mc\""
  , row1 = 4, row2 = 4
  , col1 = 0, col2 = 9
  }
]
in

--dprintLn (mapValues holeInfo.expansions);

--dprintLn (map mapBindings (mapValues holeInfo.expansions));

()
