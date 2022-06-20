import Soda.Data.Result
import Soda.Data.ByteSlice

namespace Grape

-- Idk why it's called Grape but it's the simplest implementation
-- of a parser combinator that i can think now. It will be used in
-- future things

structure ParseState where
  -- This field stores the path that the parser walked until it reached
  -- into an error (it uses the labels given by the "label" function).
  labelList : List String

-- The type synonym to a function that can fail and is feed with ByteSlice
def Grape (t: Type u): Type u :=
  ByteSlice → ParseState → (Result t)

@[inline]
def map (fn: α → β) (parser: Grape α): Grape β := λbs =>
  Result.map fn ∘ parser bs

@[inline]
def pure (result : α): Grape α := λinput _ =>
  Result.done result input

def seq (fn: Grape (α → β)) (toApp : Unit → Grape α): Grape β :=
    λinput ps => Result.map (λ⟨fn, arg⟩ => fn arg) (resultProd ps (fn input ps) toApp)
  where
    resultProd : ∀{α β : Type}, ParseState -> Result α → (Unit → Grape β) → Result (α × β)
    | ps, Result.done res inp, fn₂ => Result.map ((res, ·)) (fn₂ () inp ps)
    | _,  Result.error r err , _   => Result.error r err
    | ps, Result.cont cont   , fn₂ => Result.cont (λinput => resultProd ps (cont input) fn₂)

def bind (parserA : Grape α) (parserFn : α → Grape β): Grape β :=
    λinput ps => resultBind ps (parserA input ps) parserFn
  where
    resultBind : ParseState → Result α → (α → Grape β) → Result β
    | ps, Result.done res inp, fn₂ => fn₂ res inp ps
    | _,  Result.error r err , _   => Result.error r err
    | ps, Result.cont cont   , fn₂ => Result.cont (λinput => resultBind ps (cont input) fn₂)

instance : Monad Grape where
  map  := Grape.map
  pure := Grape.pure
  seq  := Grape.seq
  bind := Grape.bind

instance : MonadExcept String Grape where
  throw str         := λ_ st => Result.error st.labelList str
  tryCatch op onErr := λinput ps =>
    match op input ps with
    | Result.done res inp => Result.done res inp
    | Result.error _ err  => onErr err input ps
    | Result.cont cont    => Result.cont cont

instance : AndThen (Grape α) where
  andThen fst snd := fst >>= (λ_ => snd ())

instance : OrElse (Grape α) where
  orElse fst snd := tryCatch fst (λ_ => snd ())

-- Mini parser combinators

-- Probably this function is just a bad way to garantee that the parser will not continue
-- forever when there's no input.
def garantee (labelList: List String) (res: Option α) (fn: ByteSlice → Result α) (input: ByteSlice): Result α :=
  if input.size == 0
    then match res with
         | some res => Result.done res input
         | none => Result.error labelList "unexpected eof"
    else fn input

-- Takes n bytes from a byteArray
partial def Result.ByteSlice.takeN (labelList: List String) (on: Nat) (ba: ByteSlice) : Result ByteSlice :=
  if on > ba.size
    then Result.cont (garantee labelList none (takeN labelList on $ ByteSlice.heavyAppend ba ·))
    else let ⟨start, end'⟩ := ByteSlice.split ba on; Result.done start end'

-- check if bytearray is a prefix of another bytearray
partial def Result.ByteSlice.string (labelList: List String) (pref: ByteSlice) (org: ByteSlice): Result Unit :=
  match ByteSlice.isPrefixOf pref org with
  | Step.cont prefCt => Result.cont (garantee labelList none (string labelList prefCt))
  | Step.done true   => Result.done () (org.extract pref.size org.size)
  | Step.done false  => Result.error labelList "prefix not match"

-- Takes bytes until the predicate returns false.
partial def Result.ByteSlice.takeWhile (nonEmpty: Bool) (labelList: List String) (pred: UInt8 → Bool) (bs: ByteSlice): Result ByteSlice :=
    match bs.findIdx? (not ∘ pred) with
    | some idx =>
      if idx == 0 && nonEmpty == true
        then Result.error labelList "cannot match"
        else let ⟨start, end'⟩ := ByteSlice.split bs idx
             Result.done start end'
    | none =>
      Result.cont
        $ garantee labelList (some bs)
        $ Result.map (ByteSlice.heavyAppend bs) ∘ takeWhile nonEmpty labelList pred

-- Check the first byte is part of another bytearray
partial def Result.ByteSlice.oneOf (ls: List String) (bs: ByteSlice) (imp: ByteSlice): Result UInt8 :=
  if imp.size == 0
    then Result.cont (garantee ls none (oneOf ls bs))
    else match ByteSlice.findIdx? bs (· == imp[0]) with
         | some x => Result.done bs[x] (imp.extract 1 imp.size)
         | none   => Result.error ls "cannot match"

-- Checks if the first character
partial def Result.ByteSlice.byPred (ls: List String) (fn: UInt8 → Bool) (imp: ByteSlice): Result UInt8 :=
  if imp.size == 0
    then Result.cont (garantee ls none (byPred ls fn))
    else if fn imp[0]
          then Result.done imp[0] (imp.extract 1 imp.size)
          else Result.error ls "cannot match"

-- Idk why it fails to show termination so i'm using this hack that probably will last
-- until lean fix it lol

@[inline]
def string (pref: String): Grape Unit := λinp st => Result.ByteSlice.string st.labelList pref.toSlice inp

@[inline]
def takeN  (on: Nat): Grape ByteSlice := λimp ls => Result.ByteSlice.takeN ls.labelList on imp

@[inline]
def takeWhile1 (pred: UInt8 → Bool): Grape ByteSlice := λimp ls => Result.ByteSlice.takeWhile true ls.labelList pred imp

@[inline]
def takeWhile (pred: UInt8 → Bool): Grape ByteSlice := λimp ls => Result.ByteSlice.takeWhile false ls.labelList pred imp

@[inline]
def oneOf (pred: String): Grape UInt8 := λimp ls => Result.ByteSlice.oneOf ls.labelList pred.toSlice imp

@[inline]
def is (pred: UInt8 → Bool): Grape UInt8 := λimp ls => Result.ByteSlice.byPred ls.labelList pred imp

@[inline]
def eof : Grape Unit := λbs st => if bs.size == 0 then Result.done () default else Result.error st.labelList "expected eof"

def chr (chr: Char) : Grape UInt8 := is (· == chr.val.toUInt8)

-- Ones that should be generalized

@[inline]
def ignore (fst: Grape α): Grape Unit :=
  Grape.map (Function.const α ()) fst

@[inline]
def option : Grape α → Grape (Option α) :=
  λp => (map some p) <|> pure none

@[inline]
def choice : List (Thunk (Grape α)) → Grape (Option α) :=
  λopts => opts.foldl (λx y => x <|> y.get) (pure none)

@[inline]
def label (name: String) (p: Grape α) : Grape α :=
  λinp ls => p inp {ls with labelList := name :: ls.labelList}

partial def list (p: Grape α): Grape (List α) :=
  (List.cons <$> p <*> list p) <|> pure []

@[inline]
def list1 (p: Grape α): Grape (List α) :=
  List.cons <$> p <*> list p

@[inline]
def sepBy1 (p: Grape α) (s: Grape s) : Grape (List α) :=
  List.cons <$> p <*> list (s *> p)

@[inline]
def sepBy (p: Grape α) (s: Grape s) : Grape (List α) :=
  sepBy1 p s <|> pure []

@[inline]
def run (p: Grape α) (inp: ByteSlice): Result α := p inp ⟨[]⟩

end Grape
