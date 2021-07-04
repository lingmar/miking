
include "decision-points.mc"

type TuneFileFormat
con CSV : () -> TuneFileFormat
con TOML : () -> TuneFileFormat

let _listOfStrings = lam strs.
  join [strJoin ">" strs]

let tuneFileExtension = ".tune"

let tuneFileName = lam file.
  let withoutExtension =
  match strLastIndex '.' file with Some idx then
    subsequence file 0 idx
  else file
in concat withoutExtension tuneFileExtension

let tuneFileDump = lam env : CallCtxEnv. lam table : LookupTable. lam format : TuneFileFormat.
  let hole2idx = deref env.hole2idx in
  let hole2fun = deref env.hole2fun in
  let verbosePath = deref env.verbosePath in
  let callGraph = env.callGraph in

  let entry2str = lam holeInfo : NameInfo. lam path : [NameInfo]. lam i : Int.
    let funInfo : NameInfo = mapFindWithExn holeInfo hole2fun in
    let path = vertexPath i env in
    let values =
    [ int2string i
    , use MExprPrettyPrint in expr2str (get table i)
    , nameInfoGetStr holeInfo
    , info2str holeInfo.1
    , nameInfoGetStr funInfo
    , info2str funInfo.1
    , _listOfStrings (map nameInfoGetStr path)
    , _listOfStrings (map (lam x : NameInfo. info2str x.1) path)
    ] in
    match format with CSV _ then
      strJoin "," values
    else match format with TOML _ then
      strJoin "\n" (zipWith (lam x. lam y. join [x, " = ", y])
        [ indexStr
        , valueStr
        , holeNameStr
        , holeInfoStr
        , funNameStr
        , funInfoStr
        , pathNameStr
        , pathInfoStr
        ]
        values)
    else never
  in
  let taggedEntries =
    mapFoldWithKey
      (lam acc : [String]. lam h : NameInfo. lam pathMap : Map [NameInfo] Int.
         concat acc (map (lam b : ([NameInfo], Int). (b.1, entry2str h b.0 b.1)) (mapBindings pathMap)))
      [] hole2idx
  in
  let sortedTagged =
    sort (lam e1 : (Int, String). lam e2 : (Int, String). subi e1.0 e2.0)
      taggedEntries
  in
  let entries = map (lam e : (Int, String). e.1) sortedTagged in
  match format with CSV _ then
    strJoin "\n" entries
  else match format with TOML _ then
    concat "[[hole]]\n" (strJoin (join ["\n", "[[hole]]", "\n"]) entries)
  else never

