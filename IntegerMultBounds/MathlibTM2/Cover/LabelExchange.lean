module

public import IntegerMultBounds.MathlibTM2.Cover.LabelView
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.SemLeaf

/-! A single interchange call exchanges two packed label columns on a role tape. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cover.LabelExchange

open IntegerMultBounds.Machine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open LabelView (colView Swapped)

noncomputable section

theorem leafOut_swapped {u v : Descriptor} (hvol : volume prime u = volume prime v)
    (x : Fin (volume prime v) → ZMod 2) :
    Swapped prime u (ext x) (ext (RevSemantics.leafOut u hvol x)) := by
  have h := RevSemantics.leafOut_revT (u := u) (b := u.width) (one_mul _).symm hvol x
  intro a ha row hr before hb i hi mid hm j hj after he
  simpa only [revAtoms_one hi, revAtoms_one hj] using h a ha row hr before hb i
    (by simpa only [one_mul] using hi) mid hm j (by simpa only [one_mul] using hj) after he

/-- Execute an interchange view on a role carrying any equal-volume layout. -/
theorem realizes_view [M8.Machine.Net] {T : ℕ} {u v : Descriptor}
    (hvol : volume prime u = volume prime v) (hp : v.Positive)
    (io : Fin T) (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    ∃ y : Fin (volume prime v) → ZMod 2,
      GraphContract.Runs (LeafCore.core io)
        (CommonBank.bank roles (Routines.hdr u) f p node scalar ctr st)
        (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0)
          (Routines.hdr u) f p node scalar ctr st)
        (LeafCore.coreCost (volume prime v) u.width) ∧ Swapped prime u (ext x) (ext y) := by
  have hu : u.Positive := LeafCore.positive_of_volume
    (hvol ▸ RecursiveAffinePrepare.volume_positive Networks.Shared50ModularControl.prime_prime.two_le v hp)
  let y := RevSemantics.leafOut u hvol x
  refine ⟨y, ?_, ?_⟩
  · let z := fun i : Fin (volume prime u) => x (Fin.cast hvol i)
    have hrun := LeafCore.core_runs roles f p node scalar ctr st io hu z hh
      (hx.trans (LeafCore.sourceWord_cast hvol x).symm)
    have hout : sourceWord y = sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd u.rows) z) :=
      LeafCore.sourceWord_cast hvol.symm _
    rw [hout]
    apply Blocks.runs_mono hrun
    simpa only [hvol] using LeafCore.cost_le hu
  · exact leafOut_swapped hvol x

/-- With the column-view headers installed, the supplier runs once on the selected role.
Its output satisfies the interchange hypothesis of `LabelView.swap_cols` on the caller's
volume. The other roles, counters and stack are preserved. -/
theorem realizes [M8.Machine.Net] {c k s t B T : ℕ} {v : Descriptor}
    (hv : v.beforeH = B * prime ^ (k*c)) (hst : s < t) (ht : t < k) (hp : v.Positive)
    (io : Fin T) (roles : Tapes T prime) (x : Fin (volume prime v) → ZMod 2)
    (hh : roles.head io = 0) (hx : roles.tape io = sourceWord x)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (ctr : Fin CommonBank.K → Option ℕ) (st : Tapes 2 prime) :
    let u := colView prime c k s t B v
    ∃ y : Fin (volume prime v) → ZMod 2,
      GraphContract.Runs (LeafCore.core io)
        (CommonBank.bank roles (Routines.hdr u) f p node scalar ctr st)
        (CommonBank.bank (SharedPlacementAlphabet.setTape roles io (sourceWord y) 0)
          (Routines.hdr u) f p node scalar ctr st)
        (LeafCore.coreCost (volume prime v) c) ∧ Swapped prime u (ext x) (ext y) := by
  exact realizes_view (LabelView.colView_volume _ _ _ _ _ _ _ hv hst ht) hp io roles x hh hx f p node scalar ctr st

end
end IntegerMultBounds.MathlibTM2.Cover.LabelExchange
