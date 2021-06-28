include "thread.mc"
include "string.mc"

-- Mutual-exclusion locks.

-- 'mutexCreate ()' returns a new mutex.
external externalMutexCreate ! : Unit -> Mutex
let mutexCreate = lam.
  externalMutexCreate ()

-- 'mutexLock m' locks the mutex 'm'.
external externalMutexLock ! : Mutex -> Unit
let mutexLock = lam m.
  externalMutexLock m

-- 'mutexTryLock m' tries to lock the mutex 'm'.
external externalMutexTryLock ! : Mutex -> Bool
let mutexTryLock = lam m.
  externalMutexTryLock m

-- 'mutexRelease m' releases the mutex 'm'.
external externalMutexRelease ! : Mutex -> Unit
let mutexRelease = lam m.
  externalMutexRelease m

mexpr

let m = mutexCreate () in

utest mutexLock m with () in
utest mutexRelease m with () in
utest
  let b = mutexTryLock m in
  (if b then mutexRelease m else ());
  b
with true in

utest
  let ts = create 10 (lam. threadSpawn (lam.
    mutexLock m;
    -- print (join [int2string (threadSelf ()), " has the lock!"]);
    mutexRelease m
    ))
  in iter threadJoin ts
with () in

utest
  let ts = create 10 (lam. threadSpawn (lam.
    if mutexTryLock m then
      --print (join [int2string (threadSelf ()), " got the lock!"]);
      mutexRelease m
    else
      ()--print (join [int2string (threadSelf ()), " did not get the lock!"])
))
in iter threadJoin ts
with () in


()
