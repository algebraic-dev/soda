
inductive Step (α: Type) (β: Type)
  | done (res: α)
  | cont (cont: β)
  deriving Inhabited

def ByteArray.split (ba: ByteArray) (on: Nat): ByteArray × ByteArray :=
  let start' := ba.extract 0 on
  let end'   := ba.extract on ba.size
  (start', end')

partial def ByteArray.isPrefixOf (pref: ByteArray) (org: ByteArray): Step Bool ByteArray :=
    comparePrefix 0  (min pref.size org.size) true (org.size < pref.size)
  where
    comparePrefix : Nat → Nat → Bool → Bool → Step Bool ByteArray
      | idx , 0  , true , true  => (Step.cont $ pref.extract 0 idx)
      | _   , 0  , r    , false => Step.done r
      | _   , _  , false, _     => Step.done false
      | idx , n+1, _    , r     => comparePrefix (idx+1) n (pref[idx] == org[idx]) r