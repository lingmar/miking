
include "thread.mc"
include "atomic.mc"
include "channel.mc"
include "string.mc"
include "ocaml/sys.mc"

type Async a = AtomicRef (Option a)

type ThreadPoolTask
con Task : {task : Unit -> a, result : Async a} -> ThreadPoolTask
con Quit : Unit -> ThreadPoolTask

type ThreadPool = {threads : [Thread], queue : Channel ThreadPoolTask}

recursive let _wait = lam chan.
  let msg = channelRecv chan in
  match msg with Task {task = f, result = r} then
    atomicSet r (Some (f ()));
    _wait chan
  else match msg with Quit _ then ()
  else threadCPURelax (); _wait chan
end

let threadPoolCreate : Int -> ThreadPool = lam n.
  let chan = channelEmpty () in
  {threads = create n (lam. threadSpawn (lam. _wait chan)), queue = chan}

let threadPoolTearDown : ThreadPool -> Unit = lam pool.
  iter (lam. channelSend pool.queue (Quit ())) pool.threads

let threadPoolAsync : ThreadPool -> (Unit -> a) -> Async a = lam pool. lam task.
  let r = atomicMake (None ()) in
  channelSend pool.queue (Task {task = task, result = r});
  r

recursive let threadPoolWait : ThreadPool -> Async a -> a = lam pool. lam r.
  match atomicGet r with Some v then v
  else match channelRecvOpt pool.queue with Some (Task {task = f, result = r})
  then
    -- Do some work while we're waiting
    atomicSet r (Some (f ()));
    threadPoolWait pool r
  else
    threadCPURelax (); threadPoolWait pool r
end

-- Global thread pool
let threadPoolGlobal =
  let nproc = (sysRunCommand ["nproc"] "" ".").stdout in
  threadPoolCreate (string2int nproc)

mexpr

utest
  let pool = threadPoolCreate 8 in
  threadPoolTearDown pool
with () in

utest
  let pool = threadPoolCreate 4 in
  let r1 = threadPoolAsync pool (lam. addi 0 1) in
  let r2 = threadPoolAsync pool (lam. addi 0 2) in
  let r3 = threadPoolAsync pool (lam. addi 0 3) in
  let r4 = threadPoolAsync pool (lam. addi 0 4) in
  let r5 = threadPoolAsync pool (lam. addi 0 5) in
  let r =
  [ threadPoolWait pool r1
  , threadPoolWait pool r2
  , threadPoolWait pool r3
  , threadPoolWait pool r4
  , threadPoolWait pool r5
  ] in
  threadPoolTearDown pool; r
with [1,2,3,4,5] in

()
