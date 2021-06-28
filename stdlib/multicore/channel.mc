
include "atomic.mc"
include "thread.mc"
include "mutex.mc"
include "cond.mc"
include "option.mc"
include "string.mc"
include "common.mc"

-- Implements a FIFO queue with a multiple senders and multiple receiver
-- threads. The channel has an infinite buffer, so a call to channelSend never
-- blocks.

type Channel a = {contents : Aref [a], lock : Mutex, nonEmpty : Cond}

let channelEmpty : Unit -> Channel a = lam.
  { contents = atomicMake []
  , lock = mutexCreate ()
  , nonEmpty = condCreate ()
  }

-- 'channelSend c msg' sends the message 'msg' to the channel 'c'
let channelSend : Channel a -> a -> Unit = lam chan. lam msg.
  mutexLock chan.lock;

  let old = atomicGet chan.contents in
  let new = snoc old msg in
  (utest atomicCAS chan.contents old new with true in ());
  atomicSet chan.contents new;

  condSignal chan.nonEmpty;
  mutexRelease chan.lock

-- 'channelRecv c' receives a message from the channel 'c'. Blocks until there
-- is at least one message in the channel.
let channelRecv : Channel a -> a = lam chan.
  mutexLock chan.lock;

  recursive let waitForMsg : Unit -> a = lam.
    let contents = atomicGet chan.contents in
    match contents with [] then
      condWait chan.nonEmpty chan.lock;
      waitForMsg ()
    else match contents with [msg] ++ rest then
      (utest atomicCAS chan.contents contents rest with true in ());
      atomicSet chan.contents rest;
      msg
    else never
  in

  let msg = waitForMsg () in

  mutexRelease chan.lock;
  msg

-- 'channelRecvOpt c' is non-blocking version of 'channelRecv'. If the channel
-- is empty, then None () is immediately returned, instead of blocking the call.
let channelRecvOpt : Channel a -> Option a = lam chan.
  mutexLock chan.lock;

  let msg =
    let contents = atomicGet chan.contents in
    match contents with [] then None ()
    else match contents with [msg] ++ rest then
      (utest atomicCAS chan.contents contents rest with true in ());
      atomicSet chan.contents rest;
      Some msg
    else never
  in

  mutexRelease chan.lock;
  msg

mexpr

let c = channelEmpty () in

utest channelSend c 1 with () in
utest channelSend c 2 with () in
utest channelRecv c with 1 in
utest channelRecv c with 2 in

utest channelRecvOpt c with None () in
channelSend c 2;
utest channelRecvOpt c with Some 2 in

let debug = false in
let debugPrintLn = if debug then printLn else (lam x. x) in

let threads = map (lam.
  threadSpawn (lam.
    let id = int2string (threadSelf ()) in
    debugPrintLn (concat id " running");
    let res = channelRecv c in
    debugPrintLn (join [int2string (threadSelf ()), " got ", int2string res])))
  (make 10 ()) in

iteri (lam i. lam. channelSend c i) (make 10 ());

iter threadJoin threads;

()
