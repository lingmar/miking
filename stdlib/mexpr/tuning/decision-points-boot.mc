
-- Hack to be able to bootstrap 1st round with holes

type Hole
con Boolean : {default : Bool, depth : Int} -> Hole
con IntRange : {default : Int, min : Int, max : Int, depth : Int} -> Hole

let hole : Hole -> a = lam h.
  switch h
  case Boolean r then r.default
  case IntRange r then r.default
  end
