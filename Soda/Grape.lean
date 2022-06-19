import Soda.Data.Result
import Soda.Data.ByteArray

namespace Grape

-- Idk why it's called Grape but it's the simplest implementation
-- of a parser combinator that i can think now. It will be used in
-- future things

-- The type synonym to a function that can fail and is provided with ByteArray
structure ParseState where
  labelList : List String

def Grape (t: Type u): Type u := ByteArray → ParseState → (Result t)

@[inline]
def map (fn: α → β) (parser: Grape α): Grape β := λbs => Result.map fn ∘ parser bs

@[inline]
def pure (ins : α): Grape α := λinput _ => Result.done ins input

def seq (fn: Grape (α → β)) (toApp : Unit → Grape α): Grape β :=
    λinput ls => Result.map (λ⟨fn, arg⟩ => fn arg) (resultProd ls (fn input ls) toApp)
  where
    resultProd : ∀{α β : Type}, ParseState -> Result α → (Unit → Grape β) → Result (α × β)
    | ls, Result.done res inp, fn₂ => Result.map ((res, ·)) (fn₂ () inp ls)
    | _,  Result.error r err , _   => Result.error r err
    | ls, Result.cont cont   , fn₂ => Result.cont (λinput => resultProd ls (cont input) fn₂)

def bind (parserA : Grape α) (parserFn : α → Grape β): Grape β :=
    λinput ls => resultBind ls (parserA input ls) parserFn
  where
    resultBind : ParseState → Result α → (α → Grape β) → Result β
    | ls, Result.done res inp, fn₂ => fn₂ res inp ls
    | _,  Result.error r err , _   => Result.error r err
    | ls, Result.cont cont   , fn₂ => Result.cont (λinput => resultBind ls (cont input) fn₂)

instance : Monad Grape where
  map  := Grape.map
  pure := Grape.pure
  seq  := Grape.seq
  bind := Grape.bind

instance : MonadExcept String Grape where
  throw str         := λ_ st => Result.error st.labelList str
  tryCatch op onErr := λinput ls =>
    match op input ls with
    | Result.done res inp => Result.done res inp
    | Result.error _ err  => onErr err input ls
    | Result.cont cont    => Result.cont cont

instance : AndThen (Grape α) where andThen fst snd := fst >>= (λ_ => snd ())
instance : OrElse (Grape α) where orElse fst snd := tryCatch fst (λ_ => snd ())

-- Mini parser combinators

def garantee (ls: List String) (res: Option α) (fn: ByteArray → Result α) (input: ByteArray): Result α :=
  if input.size == 0
    then match res with
         | some res => Result.done res input
         | none => Result.error ls "unexpected eof"
    else fn input

partial def Result.ByteArray.takeN (ls: List String) (on: Nat) (ba: ByteArray) : Result ByteArray :=
  if on > ba.size
    then Result.cont (garantee ls none (takeN ls on $ ba ++ ·))
    else let ⟨start, end'⟩ := ByteArray.split ba on; Result.done start end'

partial def Result.ByteArray.string (ls: List String) (pref: ByteArray) (org: ByteArray): Result Unit :=
  match ByteArray.isPrefixOf pref org with
  | Step.cont prefCt => Result.cont (garantee ls none (string ls prefCt))
  | Step.done true   => Result.done () (org.extract pref.size org.size)
  | Step.done false  => Result.error ls "prefix not match"

partial def Result.ByteArray.takeWhile (nonEmpty: Bool) (ls: List String) (pred: UInt8 → Bool) (bs: ByteArray): Result ByteArray :=
    match bs.findIdx? (not $ pred ·) with
    | some n => if n == 0 && nonEmpty == true
                    then Result.error ls "cannot match"
                    else let ⟨start, end'⟩ := ByteArray.split bs n; Result.done start end'
    | none   => Result.cont (garantee ls (some bs) (Result.map (bs ++ ·) ∘ takeWhile nonEmpty ls pred))

partial def Result.ByteArray.oneOf (ls: List String) (bs: ByteArray) (imp: ByteArray): Result UInt8 :=
  if imp.size == 0
    then Result.cont (garantee ls none (oneOf ls bs))
    else match ByteArray.findIdx? bs (· == imp[0]) with
         | some x => Result.done bs[x] (imp.extract 1 imp.size)
         | none   => Result.error ls "cannot match"

partial def Result.ByteArray.byPred (ls: List String) (fn: UInt8 → Bool) (imp: ByteArray): Result UInt8 :=
  if imp.size == 0
    then Result.cont (garantee ls none (byPred ls fn))
    else if fn imp[0]
          then Result.done imp[0] (imp.extract 1 imp.size)
          else Result.error ls "cannot match"


-- Idk why it fails to show termination so i'm using this hack that probably will last
-- until lean fix it lol

@[inline]
def string (pref: String): Grape Unit := λinp st => Result.ByteArray.string st.labelList (pref.toUTF8) inp

@[inline]
def takeN  (on: Nat): Grape ByteArray := λimp ls => Result.ByteArray.takeN ls.labelList on imp

@[inline]
def takeWhile1 (pred: UInt8 → Bool): Grape ByteArray := λimp ls => Result.ByteArray.takeWhile true ls.labelList pred imp

@[inline]
def takeWhile (pred: UInt8 → Bool): Grape ByteArray := λimp ls => Result.ByteArray.takeWhile false ls.labelList pred imp

@[inline]
def oneOf (pred: String): Grape UInt8 := λimp ls => Result.ByteArray.oneOf ls.labelList pred.toUTF8 imp

@[inline]
def is (pred: UInt8 → Bool): Grape UInt8 := λimp ls => Result.ByteArray.byPred ls.labelList pred imp

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
def run (p: Grape α) (inp: ByteArray): Result α := p inp ⟨[]⟩

@[inline]
def feedResult (input: ByteArray): Result α → Result α
  | Result.done res inp => Result.done res inp
  | Result.error l err  => Result.error l err
  | Result.cont cont    => cont input

end Grape
