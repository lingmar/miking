-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Transforms an MExpr expression so that all maps are replaced by hmap.

include "assoc.mc"
include "mexpr.mc"
include "utesttrans.mc"
include "boot-parser.mc"
include "ast-builder.mc"

include "tuning/decision-points.mc"

let plib =
"
external externalAtomicMake! : (a) -> (Aref)
in
let atomicMake =
  lam v.
    externalAtomicMake
      v
in
external externalAtomicGet! : (Aref) -> (a)
in
let atomicGet =
  lam v.
    externalAtomicGet
      v
in
external externalAtomicExchange! : (Aref) -> ((a) -> (a))
in
let atomicExchange =
  lam r.
    lam v.
      externalAtomicExchange
        r
        v
in
external externalAtomicCAS! : (Aref) -> ((a) -> ((a) -> (Bool)))
in
let atomicCAS =
  lam r.
    lam v1.
      lam v2.
        externalAtomicCAS
          r
          v1
          v2
in
let atomicSet: ((ARef) (a)) -> ((a) -> (Unit)) =
  lam r.
    lam v.
      (atomicExchange
           r
           v)
      ;{}
in
type Option in
con Some: (a) -> ((Option) (a)) in
con None: (()) -> ((Option) (a)) in
let init =
  lam seq.
    subsequence
      seq
      0
      (subi
         (length
            seq)
         1)
in
let eqSeq =
  lam eq: (a) -> ((a) -> (Bool)).
    recursive
      let work =
        lam as.
          lam bs.
            let pair =
              (as, bs)
            in
            match
              pair
            with
              (\"\", \"\")
            then
              true
            else
              match
                pair
              with
                ([ a ] ++ as ++ \"\", [ b ] ++ bs ++ \"\")
              then
                match
                  eq
                    a
                    b
                with
                  true
                then
                  work
                    as
                    bs
                else
                  false
              else
                false
    in
    work
in
recursive
  let any =
    lam p.
      lam seq.
        match
          null
            seq
        with
          true
        then
          false
        else
          match
            p
              (head
                 seq)
          with
            true
          then
            true
          else
            any
              p
              (tail
                 seq)
in
let join =
  lam seqs.
    foldl
      concat
      \"\"
      seqs
in
external externalThreadSpawn! : ((Unit) -> (a)) -> (Thread)
in
let threadSpawn =
  lam f.
    externalThreadSpawn
      f
in
external externalThreadCPURelax! : (Unit) -> (Unit)
in
let threadCPURelax =
  lam u.
    externalThreadCPURelax
      u
in
let eqChar =
  lam c1.
    lam c2.
      eqc
        c1
        c2
in
let isWhitespace =
  lam c.
    any
      (eqChar
         c)
      \" \n\t\r\"
in
let eqString =
  eqSeq
    eqc
in
let string2int =
  lam s.
    recursive
      let string2int_rechelper =
        lam s.
          let len =
            length
              s
          in
          let last =
            subi
              len
              1
          in
          match
            eqi
              len
              0
          with
            true
          then
            0
          else
            let lsd =
              subi
                (char2int
                   (get
                      s
                      last))
                (char2int
                   '0')
            in
            let rest =
              muli
                10
                (string2int_rechelper
                   (subsequence
                      s
                      0
                      last))
            in
            addi
              rest
              lsd
    in
    match
      s
    with
      \"\"
    then
      0
    else
      match
        eqChar
          '-'
          (head
             s)
      with
        true
      then
        negi
          (string2int_rechelper
             (tail
                s))
      else
        string2int_rechelper
          s
in
let int2string =
  lam n.
    recursive
      let int2string_rechelper =
        lam n.
          match
            lti
              n
              10
          with
            true
          then
            [ int2char
                (addi
                   n
                   (char2int
                      '0')) ]
          else
            let d =
              [ int2char
                  (addi
                     (modi
                        n
                        10)
                     (char2int
                        '0')) ]
            in
            concat
              (int2string_rechelper
                 (divi
                    n
                    10))
              d
    in
    match
      lti
        n
        0
    with
      true
    then
      cons
        '-'
        (int2string_rechelper
           (negi
              n))
    else
      int2string_rechelper
        n
in
let strTrim =
  lam s.
    recursive
      let strTrim_init =
        lam s.
          match
            eqString
              s
              \"\"
          with
            true
          then
            s
          else
            match
              isWhitespace
                (head
                   s)
            with
              true
            then
              strTrim_init
                (tail
                   s)
            else
              s
    in
    reverse
      (strTrim_init
         (reverse
            (strTrim_init
               s)))
in
let strJoin =
  lam delim.
    lam strs.
      recursive
        let work =
          lam acc.
            lam strs.
              match
                null
                  strs
              with
                true
              then
                acc
              else
                match
                  strs
                with
                  [ s ]
                then
                  concat
                    acc
                    s
                else
                  match
                    strs
                  with
                    [ s ] ++ strs ++ \"\"
                  then
                    work
                      (concat
                         acc
                         (concat
                            s
                            delim))
                      strs
                  else
                    never
      in
      work
        \"\"
        strs
in
external externalMutexCreate! : (Unit) -> (Mutex)
in
let mutexCreate =
  lam #var\"\".
    externalMutexCreate
      {}
in
external externalMutexLock! : (Mutex) -> (Unit)
in
let mutexLock =
  lam m.
    externalMutexLock
      m
in
external externalMutexRelease! : (Mutex) -> (Unit)
in
let mutexRelease =
  lam m.
    externalMutexRelease
      m
in
external externalCondCreate! : (Unit) -> (Cond)
in
let condCreate =
  lam #var\"\".
    externalCondCreate
      {}
in
external externalCondWait! : (Cond) -> ((Mutex) -> (Unit))
in
let condWait =
  lam c.
    lam m.
      externalCondWait
        c
        m
in
external externalCondSignal! : (Cond) -> (Unit)
in
let condSignal =
  lam c.
    externalCondSignal
      c
in
type Channel =
  {lock: Mutex, contents: (Aref) ([a]), nonEmpty: Cond}
in
let channelEmpty: (Unit) -> ((Channel) (a)) =
  lam #var\"\".
    { lock =
        mutexCreate
          {},
      contents =
        atomicMake
          \"\",
      nonEmpty =
        condCreate
          {} }
in
let channelSend: ((Channel) (a)) -> ((a) -> (Unit)) =
  lam chan.
    lam msg.
      (mutexLock
           (chan.lock))
      ;let old =
        atomicGet
          (chan.contents)
      in
      let new =
        snoc
          old
          msg
      in
      (utest atomicCAS
           (chan.contents)
           old
           new
         with true
         in
         {})
      ;(atomicSet
           (chan.contents)
           new)
      ;(condSignal
           (chan.nonEmpty))
      ;mutexRelease
        (chan.lock)
in
let channelRecv: ((Channel) (a)) -> (a) =
  lam chan.
    (mutexLock
         (chan.lock))
    ;recursive
      let waitForMsg =
        lam #var\"\".
          let contents =
            atomicGet
              (chan.contents)
          in
          match
            contents
          with
            \"\"
          then
            (condWait
                 (chan.nonEmpty)
                 (chan.lock))
            ;waitForMsg
              {}
          else
            match
              contents
            with
              [ msg ] ++ rest ++ \"\"
            then
              (utest atomicCAS
                   (chan.contents)
                   contents
                   rest
                 with true
                 in
                 {})
              ;(atomicSet
                   (chan.contents)
                   rest)
              ;msg
            else
              never
    in
    let msg =
      waitForMsg
        {}
    in
    (mutexRelease
         (chan.lock))
    ;msg
in
let channelRecvOpt: ((Channel) (a)) -> ((Option) (a)) =
  lam chan.
    (mutexLock
         (chan.lock))
    ;let msg =
      let contents =
        atomicGet
          (chan.contents)
      in
      match
        contents
      with
        \"\"
      then
        None
          {}
      else
        match
          contents
        with
          [ msg ] ++ rest ++ \"\"
        then
          (utest atomicCAS
               (chan.contents)
               contents
               rest
             with true
             in
             {})
          ;(atomicSet
               (chan.contents)
               rest)
          ;Some
            msg
        else
          never
    in
    (mutexRelease
         (chan.lock))
    ;msg
in
type ExecResult =
  {stdout: [Char], stderr: [Char], returncode: Int}
in
let _pathSep =
  \"/\"
in
let _tempDirBase =
  \"/tmp\"
in
let _null =
  \"/dev/null\"
in
let _tempDirIdx =
  ref
    0
in
let _commandListTime: ([[Char]]) -> ((Float, Int)) =
  lam cmd.
    let cmd =
      strJoin
        \" \"
        cmd
    in
    let t1 =
      wallTimeMs
        {}
    in
    let res =
      command
        cmd
    in
    let t2 =
      wallTimeMs
        {}
    in
    (subf
      t2
      t1, res)
in
let _commandList =
  lam cmd: [[Char]].
    match
      _commandListTime
        cmd
    with
      (_, res)
    then
      res
    else
      never
in
let sysJoinPath =
  lam p1.
    lam p2.
      strJoin
        _pathSep
        [ p1,
          p2 ]
in
let sysTempDirMake =
  lam #var\"\".
    recursive
      let mkdir =
        lam base.
          lam i.
            let dirName =
              concat
                base
                (int2string
                   i)
            in
            match
              _commandList
                [ \"mkdir\",
                  sysJoinPath
                    _tempDirBase
                    dirName,
                  \"2>\",
                  _null ]
            with
              0
            then
              (addi
                i
                1, dirName)
            else
              mkdir
                base
                (addi
                   i
                   1)
    in
    match
      mkdir
        \"tmp\"
        (deref
           _tempDirIdx)
    with
      (i, dir)
    then
      (modref
           _tempDirIdx
           i)
      ;sysJoinPath
        _tempDirBase
        dir
    else
      never
in
let sysTempDirDelete =
  lam td.
    lam #var\"\".
      _commandList
        [ \"rm\",
          \"-rf\",
          td ]
in
let sysTimeCommand: ([[Char]]) -> (([Char]) -> (([Char]) -> ((Float, ExecResult)))) =
  lam cmd.
    lam stdin.
      lam cwd.
        let tempDir =
          sysTempDirMake
            {}
        in
        let tempStdout =
          sysJoinPath
            tempDir
            \"stdout.txt\"
        in
        let tempStderr =
          sysJoinPath
            tempDir
            \"stderr.txt\"
        in
        match
          _commandListTime
            [ \"cd\",
              cwd,
              \"&&\",
              \"echo\",
              stdin,
              \"|\",
              strJoin
                \" \"
                cmd,
              \">\",
              tempStdout,
              \"2>\",
              tempStderr ]
        with
          (ms, retCode)
        then
          (_commandList
               [ \"echo\",
                 \"\",
                 \">>\",
                 tempStdout ])
          ;(_commandList
               [ \"echo\",
                 \"\",
                 \">>\",
                 tempStderr ])
          ;let stdout =
            init
              (readFile
                 tempStdout)
          in
          let stderr =
            init
              (readFile
                 tempStderr)
          in
          (sysTempDirDelete
               tempDir
               {})
          ;(ms, { stdout =
              stdout,
            stderr =
              stderr,
            returncode =
              retCode })
        else
          never
in
let sysRunCommand: ([[Char]]) -> (([Char]) -> (([Char]) -> (ExecResult))) =
  lam cmd.
    lam stdin.
      lam cwd.
        match
          sysTimeCommand
            cmd
            stdin
            cwd
        with
          (_, res)
        then
          res
        else
          never
in
type Async =
  (AtomicRef) ((Option) (a))
in
type ThreadPoolTask in
con Task: ({task: (Unit) -> (a), result: (Async) (a)}) -> (ThreadPoolTask) in
con Quit: (Unit) -> (ThreadPoolTask) in
type ThreadPool =
  {queue: (Channel) (ThreadPoolTask), threads: [Thread]}
in
recursive
  let _wait =
    lam chan.
      let msg =
        channelRecv
          chan
      in
      match
        msg
      with
        Task {task = f, result = r}
      then
        (atomicSet
             r
             (Some
                (f
                   {})))
        ;_wait
          chan
      else
        match
          msg
        with
          Quit _
        then
          {}
        else
          never
in
let threadPoolCreate: (Int) -> (ThreadPool) =
  lam n.
    let chan =
      channelEmpty
        {}
    in
    { queue =
        chan,
      threads =
        create
          n
          (lam #var\"\".
             threadSpawn
               (lam #var\"\".
                  _wait
                    chan)) }
in
let threadPoolAsync: (ThreadPool) -> (((Unit) -> (a)) -> ((Async) (a))) =
  lam pool.
    lam task.
      let r =
        atomicMake
          (None
             {})
      in
      (channelSend
           (pool.queue)
           (Task
              { task =
                  task,
                result =
                  r }))
      ;r
in
recursive
  let threadPoolWait =
    lam pool : ThreadPool.
      lam r.
        match
          atomicGet
            r
        with
          Some v
        then
          v
        else
          match
            channelRecvOpt
              (pool.queue)
          with
            Some (Task {task = task, result = result})
          then
            (atomicSet
                 result
                 (Some
                    (task
                       {})))
            ;threadPoolWait
              pool
              r
          else
            (threadCPURelax
                 {})
            ;threadPoolWait
              pool
              r
in
let threadPoolGlobal =
  let nproc =
    (sysRunCommand
       [ \"nproc\" ]
       \"\"
       \".\").stdout
  in
  threadPoolCreate
    (string2int
       (strTrim
          nproc))
in
let pool =
  threadPoolGlobal
in
let split =
  lam seq.
    lam chunkSize.
      recursive
        let work =
          lam acc.
            lam n.
              lam xs.
                match
                  leqi
                    n
                    chunkSize
                with
                  true
                then
                  cons
                    xs
                    acc
                else
                  match
                    splitAt
                      xs
                      chunkSize
                  with
                    (chunk, xs)
                  then
                    work
                      (cons
                         chunk
                         acc)
                      (subi
                         n
                         chunkSize)
                      xs
                  else
                    never
      in
      reverse
        (work
           \"\"
           (length
              seq)
           seq)
in
let chunkWork: ([a]) -> ((([a]) -> (b)) -> ([b])) =
  lam seq.
    lam f.
      print \"chunk work!\";
      let chunkSize =
        1000000
      in
      let chunks =
        split
          seq
          chunkSize
      in
      let tasks =
        map
          (lam chunk.
             threadPoolAsync
               pool
               (lam #var\"\".
                  f
                    chunk))
          chunks
      in
      map
        (threadPoolWait
           pool)
        tasks
in
let pmap =
  lam f.
    lam seq.
      join
        (chunkWork
           seq
           (map
              f))
in
let pfold =
  lam f.
    lam acc.
      lam seq.
        foldl
          f
          acc
          (chunkWork
             seq
             (foldl
                f
                acc))
in
let piter =
  lam f.
    lam seq.
      (chunkWork
           seq
           (iter
              f))
      ;{}
in
let hmap =
  lam f.
    lam seq.
      match
        hole (Boolean {default = true, depth = 2})
      with
        true
      then
        map
          f
          seq
      else
        pmap
          f
          seq
in
let hfold =
  lam f.
    lam acc.
      lam seq.
        match
          hole (Boolean {default = true, depth = 2})
        with
          true
        then
          foldl
            f
            acc
            seq
        else
          pfold
            f
            acc
            seq
in
let hiter =
  lam f.
    lam seq.
      match
        hole (Boolean {default = true, depth = 2})
      with
        true
      then
        iter
          f
          seq
      else
        piter
          f
          seq
in
let map = lam f. lam seq.
  hmap f seq
in
let foldl = lam f. lam acc. lam seq.
  hfold f acc seq
in
let iter = lam f. lam seq. hiter f seq in
()
"

lang MapTransformer = MExpr
  sem mapTransform =
  | t ->
    use BootParser in
    let lib = parseMExprString decisionPointsKeywords plib in
    use MExprHoles in
    let lib = makeKeywords [] lib in
    let lib = symbolize lib in

    let getName = lam s.
      optionGetOrElse (lam. error (concat s " not found")) (findName s lib)
    in

    let foldName = getName "foldl" in
    let mapName = getName "map" in
    let iterName = getName "iter" in

    let constTrans = lam c.
      switch c
      case TmConst ({val = CFoldl _} & t) then TmConst t
      case TmConst {val = CMap _} then nvar_ mapName
      case TmConst ({val = CIter _} & t) then TmConst t
      case TmConst t then TmConst t
      end
    in

    let t = _mapTransform constTrans t in
    let ast = bind_ lib t in
    ast

  sem _mapTransform (f : Expr -> Expr) =
  | TmConst t ->
    f (TmConst t)
  | t ->
    smap_Expr_Expr (_mapTransform f) t
end

lang TestLang = MapTransformer + MExprSym + HolesPrettyPrint

mexpr
use TestLang in

let t = map_ (ulam_ "x" (var_ "x")) (seq_ [int_ 1]) in
let t = symbolize t in

let t = mapTransform t in

printLn (expr2str t);

()
