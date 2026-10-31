module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed
public import IntegerMultBounds.Machine.HoareWithinPlacement

/-! Prefix certificates lift through block placement independently of the
existing exact endpoint and runtime contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed
open IntegerMultBounds.Machine
open SharedBankStageInput (raw)
noncomputable section
variable {t s q a p u B C : ℕ} {M : Program s q a} {X : Tapes s a}
  {smallPost : TapePred s a} {post : TapePred (t+p) a} {lo hi : ℤ}

theorem place_within
    (h : HoareWithin M (· = X) smallPost B (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (slot : Fin s → Fin (t+p)) (hinj : Function.Injective slot) (hsize : s+u = t+p)
    (x : Tapes t a)
    (hin : ∀ i, (raw x (t+p)).head (slot i) = X.head i ∧
      (raw x (t+p)).tape (slot i) = X.tape i)
    (hframe : ∀ j, lo ≤ (raw x (t+p)).head j ∧ (raw x (t+p)).head j ≤ hi)
    (htime : HoareTime (place M slot hinj hsize).program (· = raw x (t+p)) post C) :
    HoareWithin (place M slot hinj hsize).program (· = raw x (t+p)) post C
      (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  let e := InjectivePlacement.placement slot hinj hsize
  have hactive : Placement.active e (raw x (t+p)) = X := by
    rw [InjectivePlacement.active_bank]
    apply Placement.Tapes.ext'
    · intro i; exact (hin i).1
    · intro i; exact (hin i).2
  have hp := HoareWithin.placed_heads_at h e (raw x (t+p)) hactive
    (by intro j; exact hframe (e (Fin.natAdd s j)))
  apply HoareWithin.of_time_invariant htime
  intro z hz
  exact hp.invariant hz

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed
