
@[inline]
partial def iter (op : Nat → α → α) (max: Nat) (cur: Nat) (init: α) :=
  if cur >= max
    then init
    else iter op max (Nat.succ cur) (op cur init)

def Nat.iterate {α : Sort u} (op : Nat → α → α) (max: Nat) (init: α): α := iter op max 0 init