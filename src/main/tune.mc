
-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "compile.mc"
include "options.mc"
include "mexpr/boot-parser.mc"
include "mexpr/tuning/decision-points.mc"
include "mexpr/tuning/tune.mc"
include "mexpr/tuning/warm-start.mc"
include "ocaml/sys.mc"

lang MCoreTune =
  BootParser + MExprHoles + MExprTune
end

let tableFromFile = lam file.
  printLn "tableFromFile";
  let tuneFile = tuneFileName file in
  if fileExists tuneFile then
    tuneReadTable tuneFile
  else error (join ["Tune file ", tuneFile, " does not exist"])

let tune = lam files. lam options : Options. lam args.

  let tuneFile = lam file.
    use MCoreTune in
    let ast = makeKeywords [] (parseMCoreFile decisionPointsKeywords file) in

    -- If option --debug-parse, then pretty print the AST
    (if options.debugParse then printLn (expr2str ast) else ());

    let ast = symbolize ast in
    let ast = normalizeTerm ast in

    -- Flatten the decision points
    match flatten [] ast with
      { ast = ast, table = table, tempFile = tempFile, cleanup = cleanup,
        env = env }
    then
      -- If option --use-tuned is given, then use given tune file as defaults
      let table = if options.useTuned then tableFromFile file else table in

      -- If option --try-use-tuned is given, then try to match old tune file to
      -- new program
      tryMatchHoles (tuneFileName file) env;

      -- Compile the program
      let binary = ocamlCompileAst options file ast in

      -- Runs the program with a given input
      let run = lam args : String.
        sysTimeCommand (cons (join ["./", binary]) args) "" "."
      in

      -- Do the tuning
      let result = tuneEntry args run tempFile env table in

      -- Write the best found values to filename.tune
      tuneDumpTable file (Some env) result;

      -- Clean up temporary files used during tuning
      cleanup ()
    else never
  in
  iter tuneFile files
