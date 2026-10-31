module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePad
public import IntegerMultBounds.Machine.PlacementInvariant
public import IntegerMultBounds.Machine.RunInvariant

/-! Padding preserves prefix head bounds; unselected tapes retain their initial heads. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePad
open IntegerMultBounds.Machine
open SharedBankStageInput (raw)
variable {a k : ℕ}
noncomputable section

theorem pad_heads {T₁ T₂ q : ℕ} (h : T₁ ≤ T₂) (hk : k ≤ T₁)
    (M : Program (T₁+2) q a) (x : Tapes k a) (f : ℕ) (lo hi : ℤ)
    (hM : ∀ c, RunInvariant M (· = LevelLoop.bank (raw x T₁) f) c →
      ∀ i, lo ≤ c.head i ∧ c.head i ≤ hi)
    (hbank : ∀ i, lo ≤ (LevelLoop.bank (raw x T₂) f).head i ∧
      (LevelLoop.bank (raw x T₂) f).head i ≤ hi)
    {c} {n : ℕ}
    (hrun : Machine.run (Placement.placed M (placement T₁ T₂ h)) n
      ((LevelLoop.bank (raw x T₂) f).start (Placement.placed M (placement T₁ T₂ h))) = some c) :
    ∀ i, lo ≤ c.head i ∧ c.head i ≤ hi := by
  have hstart : RunInvariant M (· = LevelLoop.bank (raw x T₁) f)
      ((Placement.active (placement T₁ T₂ h) (LevelLoop.bank (raw x T₂) f)).start M) := by
    rw [active_loop_bank h hk x f]
    exact RunInvariant.initial rfl
  have hc := (Placement.PlacedInvariant.initial hstart).run
    (fun _ _ hc hs => hc.step hs) hrun
  exact hc.heads (fun _ => lo) (fun _ => hi) hM (fun i => hbank _)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.AtomRolePad
