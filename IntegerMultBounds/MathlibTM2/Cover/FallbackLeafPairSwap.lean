module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodChildLayout
public import IntegerMultBounds.MathlibTM2.Cover.LabelExchange

/-! Run one stopped-leaf interchange on the selected pair of rank coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open FlatCoordinateLayout (rank)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem leafPairSwap_runs [M8.Machine.Net] {T r w : ℕ} (v : Descriptor) (width : v.width = r)
    (hp : v.Positive) (i : Fin r) (io : Fin T) (roles : Tapes T prime)
    (x : Fin (volume prime {v with width := w*v.width}) → ZMod 2) (hh : roles.head io = 0)
    (hx : roles.tape io = sourceWord (v := {v with width := w*v.width}) x)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (m : ℕ) (st : Tapes 2 prime) (hw : 0 < w) (free : Family.NodeFree node) :
    let parent := {v with width := w*v.width}
    ∃ y : Fin (volume prime parent) → ZMod 2,
      GraphContract.Runs (Family.leaf (LeafCore.core io))
        (CommonBank.bank roles (Routines.hdr parent) f p node scalar (Family.leafC w m r (i.val+1)) st)
        (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0)
          (Routines.hdr parent) f p node scalar (Family.leafC w m r i.val) st)
        (Family.leafCost LeafCore.coreCost parent w r) ∧
      ∀ a < v.beforeRows, ∀ row < v.rows, ∀ before < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD,
        ∀ h t : Fin r → ZMod (prime^w),
        ext y (RecursiveInterchangeLayout.index (prime^w) v a row before
          (rank (Function.update h i (t i.rev))).val mid (rank (Function.update t i.rev (h i))).val post) =
          ext x (RecursiveInterchangeLayout.index (prime^w) v a row before (rank h).val mid (rank t).val post) := by
  intro parent
  let u := {(RecursiveInterchangeLayout.child (prime^w) 1 1 v i i.rev) with width := w}
  have usize : volume prime u = volume prime parent := by
    have same := RecursiveInterchangeLayout.child_volume_div (prime^w) 1 1 v i i.rev
      (by simpa using width) (by decide) (one_dvd _)
    simpa [u,parent,volume,RecursiveInterchangeLayout.child,pow_mul] using same
  let y := RevSemantics.leafOut u usize x
  have swap := LabelExchange.leafOut_swapped usize x
  have view : sub prime w r i.val 1 parent = u := by
    simp [sub,u,parent,RecursiveInterchangeLayout.child,pow_mul,Nat.mul_comm,Nat.sub_sub,Nat.add_comm]
    exact Or.inl (congrArg ((prime^w)^·) (by omega))
  refine ⟨y,?_,?_⟩
  · apply RevSemantics.leaf_runs_of (LeafCore.leafCore97 io).1 (show parent.Positive from hp) hw
      (by simp [parent,width,Nat.mul_comm]) (Nat.succ_pos _) i.isLt free
    intro node' ctr
    simp only [Nat.add_one_sub_one,view]
    exact LabelExchange.leafOut_runs usize hp io roles x hh hx f p node' scalar ctr st

  · intro a ha row hr before hb mid hm post he h t
    have effect := leafPair_apply v width prime w rfl i Prod.swap (ext x) (ext y)
      h t a row before mid post hb hm he (by
        intro pre hpre middle hmid after hpost z s
        exact swap a ha row (by simpa [u,RecursiveInterchangeLayout.child] using hr) pre hpre
          s.val s.val_lt middle hmid z.val z.val_lt after hpost)
    exact effect

/-- Exchange two adjacent equal-width blocks on the role tape. Prefix and
suffix are arbitrary, so this also applies to a block inside a larger rotation. -/
theorem packAdjacent_runs [M8.Machine.Net] {T w heads suffix : ℕ}
    (v : Descriptor) (hp : v.Positive) (size : heads*(prime^w*(prime^w*suffix)) = volume prime v)
    (io : Fin T) (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let view : Descriptor := ⟨heads,1,1,w,1,suffix⟩
    ∃ y : Fin (volume prime v) → ZMod 2,
      GraphContract.Runs (LeafCore.core io)
        (CommonBank.bank roles (Routines.hdr view) f p node scalar ctr st)
        (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0)
          (Routines.hdr view) f p node scalar ctr st)
        (LeafCore.coreCost (volume prime v) w) ∧
      ∀ i, y ((packMiddleTail heads (prime^w) (prime^w) suffix i).cast size) = x (i.cast size) := by
  intro view
  have same : volume prime view = volume prime v := by
    simpa [view,volume,Nat.mul_assoc] using size
  obtain ⟨y,run,swap⟩ := LabelExchange.realizes_view same hp io roles x hh hx f p node scalar ctr st
  refine ⟨y,run,?_⟩
  intro i
  obtain ⟨⟨h,rest⟩,rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨m,rest⟩,rfl⟩ := finProdFinEquiv.surjective rest
  obtain ⟨⟨t,j⟩,rfl⟩ := finProdFinEquiv.surjective rest
  rw [packMiddleTail_index]
  have cell := swap h h.isLt 0 Nat.zero_lt_one 0 Nat.zero_lt_one t t.isLt 0 Nat.zero_lt_one m m.isLt j j.isLt
  have addr (a b : Fin (prime^w)) :
      RecursiveInterchangeLayout.index prime view h 0 0 a 0 b j =
        (finProdFinEquiv (h,finProdFinEquiv (a,finProdFinEquiv (b,j)))).val := by
    simp only [RecursiveInterchangeLayout.index,view,Nat.mul_one,Nat.add_zero,finProdFinEquiv,Equiv.coe_fn_mk]
    ring
  rw [addr,addr] at cell
  have inside (a b : Fin (prime^w)) :
      (finProdFinEquiv (h,finProdFinEquiv (a,finProdFinEquiv (b,j)))).val < volume prime v :=
    size ▸ (finProdFinEquiv (h,finProdFinEquiv (a,finProdFinEquiv (b,j)))).isLt
  simp only [ext,dite_eq_left (inside t m),dite_eq_left (inside m t)] at cell
  exact cell

/-- Every scheduled atom exchange uses the same core width and volume. Only the
prefix and suffix headers vary with the position. -/
theorem scheduledPack_runs [M8.Machine.Net] {T w heads middle tail suffix i : ℕ}
    (used : i ∈ middleTailSchedule middle tail) (v : Descriptor) (hp : v.Positive)
    (size : heads*(prime^w)^(middle+tail)*suffix = volume prime v)
    (io : Fin T) (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let M := prime^w
    let pre := heads*M^i
    let post := M^(middle+tail-(i+2))*suffix
    let view : Descriptor := ⟨pre,1,1,w,1,post⟩
    ∃ (width : pre*(M*(M*post)) = volume prime v) (y : Fin (volume prime v) → ZMod 2),
      GraphContract.Runs (LeafCore.core io)
        (CommonBank.bank roles (Routines.hdr view) f p node scalar ctr st)
        (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0)
          (Routines.hdr view) f p node scalar ctr st)
        (LeafCore.coreCost (volume prime v) w) ∧
      ∀ j, y ((packMiddleTail pre M M post j).cast width) = x (j.cast width) := by
  intro M pre post view
  have inside := middleTailSchedule_inside used
  have split : M^(middle+tail) = M^i*M^2*M^(middle+tail-(i+2)) := by
    rw [← pow_add,← pow_add,show i+2+(middle+tail-(i+2)) = middle+tail by omega]
  have width : pre*(M*(M*post)) = volume prime v := by
    change heads*M^(middle+tail)*suffix = _ at size
    rw [← size,split]
    dsimp only [pre,post]
    ring
  exact ⟨width,packAdjacent_runs v hp width io roles x hh hx f p node scalar ctr st⟩

theorem middleTailSchedule_coreCost [M8.Machine.Net] (middle tail V w : ℕ) :
    ((middleTailSchedule middle tail).map fun _ => LeafCore.coreCost V w).sum =
      tail*middle*LeafCore.coreCost V w := by
  simp [middleTailSchedule_length]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
