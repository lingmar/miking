let foo = lam.
  sleepMs (hole (IntRange {min = 0, max = 1000, default = 1000}))

mexpr

foo ()
