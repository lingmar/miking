-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt

include "compile.mc"
include "options.mc"
include "mexpr/boot-parser.mc"
include "mexpr/tuning/decision-points.mc"
include "mexpr/tuning/tune.mc"
include "mexpr/seq-transformer.mc"
include "mexpr/tuning/transfer-tuning.mc"
include "ocaml/sys.mc"

lang MCoreTune =
  BootParser + MExprHoles + MExprTune
end

let tableFromFile = lam file.
  if fileExists file then
    tuneReadTable file
  else
    error (join ["Tune file ", file, " does not exist"])

let getTuneFile = lam options : Options. lam file. lam tuneFiles.
  if options.useDefaultTuneFile then
    tuneFileName file
  else match tuneFiles with [tuneFile] ++ _ then
    tuneFile
  else error "No tune file provided"

let transferTune = lam options : Options. lam table. lam file. lam tuneFiles. lam env.
  if options.transferTune then
    transferTune (getTuneFile options file tuneFiles) env
  else table

let tune = lam files. lam options : Options. lam args.

  match partition (isSuffix eqc ".tune") files with (tuneFiles, nonTunes) then
  match partition stringIsInt nonTunes with (n, files) then

    let tuneFile = lam file.
      use MCoreTune in
      let ast = makeKeywords [] (parseMCoreFile decisionPointsKeywords file) in

      -- If option --enable-seq-transform, then transform sequence literals into
      -- using create
      let ast = seqTransform options n ast in

      -- If option --enable-map-transform, then transform maps into using hmap
      let ast = mapTransform options ast in

      -- If option --debug-parse, then pretty print the AST
      (if options.debugParse then printLn (expr2str ast) else ());

      let ast = symbolize ast in
      let ast = normalizeTerm ast in

      printLn "before flattening";

      let t1 = wallTimeMs () in
      -- Flatten the decision points
      match flatten [] ast with
        { ast = ast, table = table, tempFile = tempFile, cleanup = cleanup,
          env = env, tempDir = tempDir }
      then
        let t2 = wallTimeMs () in

        print "flattening time = "; dprint (divf (subf t2 t1) 1000.); flushStdout ();
        -- printLn (use MExprPrettyPrint in expr2str ast);

        -- If option --use-tuned is given, then use given tune file as defaults
        let table =
          if options.useTuned then
            tableFromFile (getTuneFile options file tuneFiles)
          else table
        in

        -- If option --transfer-tune is given, then try to match old tune file to
        -- new program
        let t1 = wallTimeMs () in
        let table = transferTune options table file tuneFiles env in
        let t2 = wallTimeMs () in
        print "transfer tuning time = "; dprint (divf (subf t2 t1) 1000.);
        flushStdout ();

        -- Compile the program and move to temporary directory
        let t1 = wallTimeMs () in

        let binary = ocamlCompileAst
          {options with destination = Some (sysJoinPath tempDir "tune")} file ast
        in

        let t2 = wallTimeMs () in
        print "compilation time = "; dprint (divf (subf t2 t1) 1000.); flushStdout ();

        -- Runs the program with a given input
        let run = lam args : String.
          sysTimeCommand (cons binary args) "" "."
        in

        -- Do the tuning
        let result = tuneEntry args run tempFile env table in

        -- Write the best found values to filename.tune
        tuneDumpTable file (Some env) result;

        -- If option --compile is given, then compile the program using the
        -- tuned values
        (if options.compileAfterTune then
           compile nonTunes {options with useTuned = true} args
         else ());

        -- Clean up temporary files used during tuning
        cleanup ()
      else never
    in
    iter tuneFile files
  else never else never
