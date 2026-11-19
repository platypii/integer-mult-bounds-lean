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

end IntegerMultBounds.MathlibTM2.Cover.Fallback
