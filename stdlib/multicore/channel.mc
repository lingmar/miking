
include "atomic.mc"
include "thread.mc"
include "option.mc"
include "string.mc"
include "common.mc"

-- Implements a FIFO queue with a single sender and multiple receiver threads.
-- The channel has an infinite buffer, so a call to channelSend never blocks.

type Channel a = {contents : Aref [a], receivers : Aref [Int]}

let channelEmpty : Unit -> Channel a = lam.
  {contents = atomicMake [], receivers = atomicMake []}

-- Wake up receivers
recursive let channelSend : Channel a -> a -> Unit = lam chan. lam msg.
  let old = atomicGet chan.contents in
  let new = snoc old msg in
  if atomicCAS chan.contents old new then
    recursive let wakeUpRecv = lam.
      let waiting = atomicGet chan.receivers in
      if null waiting then ()
      else if atomicCAS chan.receivers waiting (tail waiting) then
        -- Wake up one receiver
        threadNotify (head waiting)
      else
        threadCPURelax ();
        wakeUpRecv ()
    in wakeUpRecv ()
  else threadCPURelax (); channelSend chan msg
end

recursive let channelRecv : Channel a -> a = lam chan.
  let contents = atomicGet chan.contents in
  match contents with [] then
    threadCriticalSection (lam.
      recursive let addToReceivers = lam.
        let receivers = atomicGet chan.receivers in
        if atomicCAS chan.receivers receivers (snoc receivers (threadSelf ()))
        then ()
        else
          threadCPURelax ();
          addToReceivers ()
      in
      addToReceivers ();
      -- Wait here until there are tasks available
      threadWait ());
    channelRecv chan
  else match contents with [msg] ++ new then
    if atomicCAS chan.contents contents new then
      -- Got the message
      msg
    else
      -- Someone else got there first, try again
      threadCPURelax ();
      channelRecv chan
  else never
end

let channelRecvOpt : Channel a -> Option a = lam chan.
  let contents = atomicGet chan.contents in
  match contents with [] then None ()
  else if atomicCAS chan.contents contents (tail contents) then
    Some (head contents)
  else None ()

mexpr

let c = channelEmpty () in

utest channelSend c 1 with () in
utest channelSend c 2 with () in
utest channelRecv c with 1 in
utest channelRecv c with 2 in

utest channelRecvOpt c with None () using optionEq eqi in
channelSend c 2;
utest channelRecvOpt c with Some 2 using optionEq eqi in

let debug = false in
let debugPrintLn = if debug then printLn else (lam x. x) in

let threads = map (lam.
  threadSpawn (lam.
    let id = int2string (threadSelf ()) in
    debugPrintLn (concat id " running");
    let res = channelRecv c in
    debugPrintLn (join [int2string (threadSelf ()), " got ", int2string res])))
  (make 10 ()) in

mapi (lam i. lam. channelSend c i) (make 10 ());

iter threadJoin threads;

()
