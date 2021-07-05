include "tune-file.mc"
include "kd-tree.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"

type HoleInfo =
{ varName : String
, ty : Int
, value : Int  -- if Bool then 0=false, 1=true
, varInfo : Info
, funName : String
, funInfo : Info
, pathName : [String]
, pathInfo : [Info]
}

let holeInfo2str = lam h : HoleInfo.
  strJoin ","
  [ h.varName
  , int2string h.ty
  , int2string h.value
  , info2str h.varInfo
  , h.funName
  , info2str h.funInfo
  , strJoin ">" h.pathName
  , strJoin ">" (map info2str h.pathInfo)
  ]

let _defaultLineNo = 0
let _defaultFunName = ""
let _defaultFileName = ""
let _defaultInfoFile = lam i.
  match i with Info {filename = filename} then filename else _defaultFileName
let _defaultInfoLineNo = lam i.
match i with Info {row1 = row1} then row1 else _defaultLineNo

let _padOrCutToLen = lam n. lam v. lam seq.
  let len = length seq in
  if eqi len n then seq
  else if gti len n then subsequence seq 0 n
  else concat seq (create (subi n len) (lam. v))

utest _padOrCutToLen 4 0 [1,2] with [1,2,0,0]
utest _padOrCutToLen 3 1 [1,2,3] with [1,2,3]
utest _padOrCutToLen 3 1 [1,2,3,4] with [1,2,3]

recursive let _interleaved = lam acc. lam i. lam n. lam s1. lam s2. lam s3.
  if eqi i n then acc
  else _interleaved (concat acc [get s1 i, get s2 i, get s3 i]) (addi i 1) n s1 s2 s3
end

utest _interleaved [] 0 3 [1,2,3] [4,5,6] [7,8,9] with [1,4,7,2,5,8,3,6,9]

let asciiSum = lam s : String.
  foldl (lam acc. lam c. addi acc (char2int c)) 0 s

let createPoint = lam d : Int. lam h : HoleInfo.
  let funNames = map asciiSum (_padOrCutToLen d _defaultFunName (reverse h.pathName)) in
  let pathInfos = reverse h.pathInfo in
  let funFileNames = map asciiSum (
    _padOrCutToLen d _defaultFileName
      (map _defaultInfoFile pathInfos)
  ) in
  let funLineNos = _padOrCutToLen d _defaultLineNo
    (map _defaultInfoLineNo pathInfos)
  in
  concat
  [ asciiSum h.varName
  , _defaultInfoLineNo h.varInfo
  ]
  (_interleaved [] 0 d funNames funFileNames funLineNos)

utest
createPoint 2
{ varName = "a"
, ty = 0
, value = true
, varInfo = Info {filename = "", row1 = 42, col1 = 0, row2 = 0, col2 = 0}
, funName = "foo"
, funInfo = Info {filename = "", row1 = 3, col1 = 0, row2 = 0, col2 = 0}
, pathName = ["test", "bar", "foo"]
, pathInfo =
  [ Info {filename = "testfile", row1 = 1, col1 = 0, row2 = 0, col2 = 0}
  , NoInfo ()
  , Info {filename = "foofile", row1 = 3, col1 = 0, row2 = 0, col2 = 0}
  ]
}
with
[ 97, 42
, 324, 740, 3
, 309, 0, 0]

let _strIndex = lam c. lam s.
  let n = length s in
    recursive let work = lam i.
    if geqi i n then None ()
    else if eqc c (get s i) then Some i
    else work (addi i 1)
  in work 0

let tuneFile2holeInfo : String -> [HoleInfo] = lam file : String.
  let holeInfoFromRow = lam row : String.
    let vals = strSplit "," row in
    let ty = string2int (get vals typeIdx) in
    { ty = ty
    , val =
      if eqi ty boolTypeValue then
        switch get vals valueIdx
        case "false" then 0
        case "true" then 1
        end
      else if eqi ty intTypeValue then string2int (get vals valueIdx)
      else error (concat "unknown type value: " (int2string ty))
    , varName = get vals holeNameIdx
    , varInfo = str2info (get vals holeInfoIdx)
    , funName = get vals funNameIdx
    , funInfo = str2info (get vals funInfoIdx)
    , pathName = strSplit "<" (get vals pathNameIdx)
    , pathInfo = map str2info (strSplit ">" (get vals pathInfoIdx))
    }
  in

  let str = readFile file in
  match _strIndex '=' str with Some i then
    match splitAt str i with (_, str) then
      let rows = tail (strSplit "\n" (strTrim str)) in
      let entries = map holeInfoFromRow rows in
      entries
    else never
  else error (concat "Cannot parse tune file " file)

let env2holeInfo : CallCtxEnv -> [HoleInfo] = lam env : CallCtxEnv.
  match env
  with
    { hole2idx = hole2idx, hole2fun = hole2fun, hole2ty = hole2ty }
  then
    let hole2idx = deref hole2idx in
    let hole2fun = deref hole2fun in
    let hole2ty = deref hole2ty in
    foldl (lam acc : [HoleInfo]. lam bind : (NameInfo, Map [NameInfo] Int).
      let holeName : String = nameInfoGetStr bind.0 in
      let holeInfo : Info = nameInfoGetInfo bind.0 in
      let ty = use MExprAst in
        switch mapFindWithExn bind.0 hole2ty
        case TyBool _ then boolTypeValue
        case TyInt _ then intTypeValue
        end
      in
      let funNameInfo : NameInfo = mapFindWithExn bind.0 hole2fun in
      let funName : String = nameInfoGetStr funNameInfo in
      let funInfo : Info = nameInfoGetInfo funNameInfo in
      concat acc (
        foldl (lam acc : [HoleInfo]. lam path : [NameInfo].
          let i = mapFindWithExn path bind.1 in
          let pathVerbose = vertexPath bind.0 i env in
          match unzip pathVerbose with (funNames, funInfos) then
            let funNames : [String] = map nameGetStr funNames in
            snoc acc
              { varName = holeName
              , ty = ty
              , value = i -- index in table
              , varInfo = holeInfo
              , funName = funName
              , funInfo = funInfo
              , pathName = funNames
              , pathInfo = funInfos
              }
          else never
        ) [] (mapKeys bind.1)
      )
    ) [] (mapBindings hole2idx)
  else never

let _inRange = lam min. lam max. lam v.
  use MExprAst in
  match v with TmConst {val = CInt {val = i}} then
    if gti i max then int_ max
    else if lti i min then int_ min
    else v
  else error "impossible"

let transferValues = lam env : CallCtxEnv. lam matched : Map Int Expr.
  match env with {idx2hole = idx2hole} then
    let idx2hole = deref idx2hole in
    let n = length idx2hole in
    recursive let buildTable = lam acc. lam i.
      if eqi i n then acc
      else
        let val =
          use MExprHoles in
          match mapLookup i matched with Some expr then
            match get idx2hole i
            with TmHole {inner = HIntRange {min = min, max = max}} then
              _inRange min max expr
            else expr
          else default (get idx2hole i)
        in buildTable (snoc acc val) (addi i 1)
    in
    buildTable [] 0
  else never

let transferTune = lam file. lam env.
  printLn "in transferTune";

  -- Parse all holes into common info data structure
  let old = tuneFile2holeInfo file in
  printLn "tune file parsed";
  let new = env2holeInfo env in
  printLn "env parsed";

  printLn "after parse";

  -- Partition by types
  let oldBoolInt = partition (lam x : HoleInfo. eqi x.ty boolTypeValue) old in
  let newBoolInt = partition (lam x : HoleInfo. eqi x.ty boolTypeValue) new in

  let oldBool = oldBoolInt.0 in
  let oldInt = oldBoolInt.1 in
  let newBool = newBoolInt.0 in
  let newInt = newBoolInt.1 in

  printLn "after partition";

  -- Dimensions of the problem
  let pathLen = 3 in
  let dim = 11 in

  -- Create data points
  let oldPointsBool = map (createPoint pathLen) oldBool in
  let oldPointsInt = map (createPoint pathLen) oldInt in
  let newPointsBool = map (createPoint pathLen) newBool in
  let newPointsInt = map (createPoint pathLen) newInt in

  -- Prepend the points with integer identifiers
  let count = lam points.
    let r = ref 0 in
    map (lam p. let v = deref r in modref r (addi 1 v); cons v p) points
  in

  let oldPointsBool = count oldPointsBool in
  let oldPointsInt = count oldPointsInt in
  let newPointsBool = count newPointsBool in
  let newPointsInt = count newPointsInt in

  printLn "finished data points";

  -- Create kd-trees from old points and find nearest neighbors
  let valMap =
    lam acc : Map Int Expr.
    lam oldPoints. lam newPoints.
    lam oldInfos : [HoleInfo].
    lam newInfos : [HoleInfo].
    lam convert : Int -> Expr.
      match oldPoints with [] then
        mapEmpty subi
      else
        let tree = kdTreeCreate subi dim oldPoints in
        let nearest = map (kdTreeNearest dim tree) newPoints in
        foldl (lam acc. lam pair : (HoleInfo, Nearest).
          let h = pair.0 in
          let nearest = pair.1 in
          match nearest with {nearest = nearest} then
            let iOld = head nearest in
            let oldHole : HoleInfo = get oldInfos iOld in
            print "new hole "; printLn (holeInfo2str h);
            print "old hole "; printLn (holeInfo2str oldHole);
            let expr = convert oldHole.value in
            let iNew = h.value in
            mapInsert iNew expr acc
          else never
        ) acc (zip newInfos nearest)
  in
  let valsBool = valMap (mapEmpty subi) oldPointsBool newPointsBool
    oldBool newBool (lam v. switch v case 0 then false_ case 1 then true_ end)
  in
  let valsInt = valMap valsBool oldPointsInt newPointsInt
    oldInt newInt int_
  in

  let vals = valsInt in

  printLn "finished transfer";

  let res = transferValues env vals in

  printLn "finished table";

  res

mexpr

use MExprEq in

tuneFile2holeInfo "test/examples/tuning/test.tune";

utest _inRange 1 10 (int_ 3) with int_ 3 using eqExpr in
utest _inRange 1 10 (int_ 11) with int_ 10 using eqExpr in
utest _inRange 1 10 (int_ 0) with int_ 1 using eqExpr in

()
