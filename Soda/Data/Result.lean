import Init.Data.Format.Basic
import Soda.Data.ByteSlice

inductive Result (α: Type u) : Type u
  | done  (result: α) (rest: ByteSlice)
  | error (err: List String) (err: String)
  | cont  (fn: ByteSlice → Result α)
  deriving Inhabited

instance [Repr α] : Repr (Result α) where
  reprPrec
    | Result.done x r, _    => "Done(" ++ repr x ++ "," ++ toString r ++ ")"
    | Result.error ls x, _  => "Error(" ++ repr x ++ " " ++ repr ls ++ ")"
    | Result.cont _,  _     => "Continuation"

def Result.map (fn: α → β): Result α → Result β
  | Result.done res i       => Result.done (fn res) i
  | Result.error labels err => Result.error labels err
  | Result.cont gen         => Result.cont (λinp => map fn (gen inp))

@[inline]
def Result.feedResult (input: ByteArray): Result α → Result α
  | Result.done res inp => Result.done res inp
  | Result.error l err  => Result.error l err
  | Result.cont fnCont  => fnCont ⟨input, 0, input.size⟩

instance : Functor Result where map := Result.map