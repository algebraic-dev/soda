import Soda.Data.Nat

structure ByteSlice where
  arr  : ByteArray
  off  : Nat
  size : Nat

instance : Inhabited ByteSlice where
  default := ⟨default, 0, 0⟩

inductive Step (α: Type) (β: Type)
  | done (res: α)
  | cont (cont: β)
  deriving Inhabited

def String.toSlice (s: String): ByteSlice := ⟨s.toUTF8, 0, s.length⟩
def ByteArray.toSlice (s: ByteArray): ByteSlice := ⟨s, 0, s.size⟩

namespace ByteSlice

@[inline]
def toChar : UInt8 → Char := Char.ofNat ∘ UInt8.toNat

@[inline]
def getIdx (self: ByteSlice) (idx: Nat) : UInt8 := self.arr[self.off + idx]

def getByteArray (self: ByteSlice): ByteArray := self.arr.extract self.off (self.off + self.size)

def heavyAppend (bs: ByteSlice) (en: ByteSlice): ByteSlice :=
  if bs.size == 0 then en else (if en.size == 0 then bs else (bs.getByteArray ++ en.getByteArray).toSlice)

def toASCIIString (bs: ByteSlice): String :=
  Nat.iterate
    (λidx str => str.push (toChar $ bs.getIdx idx))
    bs.size
    ""

def getOp (self: ByteSlice) (idx: Nat) : UInt8 :=
  if idx >= self.size
    then panic! "idx out of bounds :'<"
    else self.getIdx idx

instance : ToString ByteSlice where toString e := s!"⟨\"{e.toASCIIString}\",{e.off}, {e.size}⟩"

def findIdx? (self: ByteSlice) (fn: UInt8 → Bool) : Option Nat :=
    contains' self.size 0 self
  where
    contains' : Nat → Nat → ByteSlice → Option Nat
      | Nat.zero ,  _, _ => none
      | Nat.succ m, n, s =>
        if fn s[n]
          then some n
          else contains' m (n + 1) s

def extractLen (ba: ByteSlice) (start: Nat) (size: Nat): ByteSlice :=
  let startPos := ba.off + start
  ⟨ba.arr, startPos, size⟩

@[inline]
def extract (ba: ByteSlice) (start: Nat) (en': Nat): ByteSlice := extractLen ba start (en' - start)

def split (ba: ByteSlice) (on: Nat): ByteSlice × ByteSlice :=
  if on > ba.size
    then ⟨ba, default⟩
    else let start' := ba.extractLen 0 on
         let end'   := ba.extract on ba.size
         (start', end')

partial def isPrefixOf (pref: ByteSlice) (org: ByteSlice): Step Bool ByteSlice :=
    comparePrefix 0 (min pref.size org.size) true (org.size < pref.size)
  where
    comparePrefix : Nat → Nat → Bool → Bool → Step Bool ByteSlice
      | idx , 0  , true , true  => (Step.cont $ pref.extract 0 idx)
      | _   , 0  , res  , false => Step.done res
      | _   , _  , false, _     => Step.done false
      | idx , n+1, _    , lesst => comparePrefix (idx+1) n (pref[idx] == org[idx]) lesst

end ByteSlice