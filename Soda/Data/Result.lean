import Init.Data.Format.Basic

inductive Result (α: Type u) : Type u
  | done  (result: α) (rest: ByteArray)
  | error (err: List String) (err: String)
  | cont  (fn: ByteArray → Result α)
  deriving Inhabited

instance [ToString α] : Repr (Result α) where
  reprPrec
    | Result.done x r, _   => "Done(" ++ toString x ++ "," ++ toString r ++ ")"
    | Result.error ls x, _  => "Error " ++ repr x ++ " " ++ repr ls
    | Result.cont _,  _    => "Continuation"

instance [Repr α] : Repr (Result α) where
  reprPrec
    | Result.done x r, _   => "Done(" ++ repr x ++ "," ++ toString r ++ ")"
    | Result.error ls x, _  => "Error " ++ repr x ++ " " ++ repr ls
    | Result.cont _,  _    => "Continuation"

instance [ToString α]  : ToString (Result α) where toString := reprStr

@[inline]
def Result.map (f: α → β): Result α → Result β
  | Result.done res i   => Result.done (f res) i
  | Result.error r res  => Result.error r res
  | Result.cont gen     => Result.cont (λinp => map f (gen inp))

instance : Functor Result where map := Result.map