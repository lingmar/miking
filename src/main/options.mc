include "assoc.mc"
include "common.mc"
include "option.mc"
include "string.mc"

type Options = {
  debugParse : Bool,
  debugGenerate : Bool,
  debugTypeAnnot : Bool,
  exitBefore : Bool,
  runTests : Bool,
  disableOptimizations : Bool,
  useTuned : Bool,
  seqTransform : Bool,
  mapTransform : Bool,
  help : Bool,
  transferTune : Bool,
  useDefaultTuneFile : Bool,
  compileAfterTune : Bool
}

-- Option structure
let options = {
  debugParse = false,
  debugGenerate = false,
  debugTypeAnnot = false,
  exitBefore = false,
  runTests = false,
  disableOptimizations = false,
  useTuned = false,
  seqTransform = false,
  mapTransform = false,
  help = false,
  transferTune = false,
  useDefaultTuneFile = false,
  compileAfterTune = false
}

-- Option map, maps strings to structure updates
let optionsMap = [
("--debug-parse", lam o : Options. {o with debugParse = true}),
("--debug-generate", lam o : Options. {o with debugGenerate = true}),
("--debug-type-annot", lam o : Options. {o with debugTypeAnnot = true}),
("--exit-before", lam o : Options. {o with exitBefore = true}),
("--test", lam o : Options. {o with runTests = true}),
("--disable-optimizations", lam o : Options. {o with disableOptimizations = true}),
("--tuned", lam o : Options. {o with useTuned = true}),
("--enable-seq-transform", lam o : Options. {o with seqTransform = true}),
("--enable-map-transform", lam o : Options. {o with mapTransform = true}),
("--help", lam o : Options. {o with help = true}),
("--transfer-tune", lam o : Options. {o with transferTune = true}),
("--default-tune-file", lam o : Options. {o with useDefaultTuneFile = true}),
("--compile", lam o : Options. {o with compileAfterTune = true})
]

let mapStringLookup = assocLookup {eq=eqString}

-- Simple handling of options before we have an argument parsing library.
let parseOptions = lam xs.
  foldl
    (lam accOps. lam s.
      match mapStringLookup s optionsMap with Some f
      then f accOps
      else printLn (concat "Unknown option " s); exit 1
    ) options xs

-- Split the program arguments before and after the empty '--'
let splitDashDash = lam lst.
  match index (eqString "--") lst with Some n then
    let r = splitAt lst n in
    {first = r.0, last = tail r.1}
  else
    {first = lst, last = []}
