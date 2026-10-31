module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed
public import IntegerMultBounds.Machine.PlacementInvariant
public import IntegerMultBounds.Machine.RunInvariant

/-! Prefix space bounds lift through the same bank read used by block execution.
Spectators retain their original heads. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed
open IntegerMultBounds.Machine
open SharedBankStageInput (raw)
noncomputable section
variable {t s q a p u : ℕ}

theorem place_heads (M : Program s q a) (X : Tapes s a)
    (slot : Fin s → Fin (t+p)) (hinj : Function.Injective slot) (hsize : s+u = t+p)
    (x : Tapes t a)
    (hin : ∀ i, (raw x (t+p)).head (slot i) = X.head i ∧
      (raw x (t+p)).tape (slot i) = X.tape i)
    (B : ℕ)
    (hM : ∀ c, RunInvariant M (· = X) c →
      ∀ i, X.head i-B ≤ c.head i ∧ c.head i ≤ X.head i+B)
    {c} {n : ℕ}
    (hrun : Machine.run (place M slot hinj hsize).program n
      ((raw x (t+p)).start (place M slot hinj hsize).program) = some c) :
    ∀ i, (raw x (t+p)).head i-B ≤ c.head i ∧ c.head i ≤ (raw x (t+p)).head i+B := by
  let e := InjectivePlacement.placement slot hinj hsize
  have hactive : Placement.active e (raw x (t+p)) = X := by
    rw [InjectivePlacement.active_bank]
    apply Placement.Tapes.ext'
    · intro i; exact (hin i).1
    · intro i; exact (hin i).2
  have hstart : RunInvariant M (· = X) ((Placement.active e (raw x (t+p))).start M) := by
    rw [hactive]
    exact RunInvariant.initial rfl
  have hc := (Placement.PlacedInvariant.initial hstart).run
    (fun _ _ hc hs => hc.step hs) hrun
  apply hc.heads (fun i => (raw x (t+p)).head i-B) (fun i => (raw x (t+p)).head i+B)
  · intro z hz i
    simp only [e,InjectivePlacement.active_slot]
    rw [(hin i).1]
    exact hM z hz i
  · intro i
    dsimp only [Placement.extra]
    constructor <;> omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.Embed
