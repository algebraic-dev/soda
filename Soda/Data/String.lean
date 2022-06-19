@[inline] def String.oneOf (str: String) (pred: UInt8): Bool :=
  Option.isSome $ str.toUTF8.findIdx? (· == pred)

@[inline] def String.noneOf (str: String): UInt8 → Bool := not ∘ str.oneOf