module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! A native push certificate remains valid under a larger fixed allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Stack
variable {K σ P : Type} {Γ : K → Type} {c d : ℕ}

theorem mnNativePushBound_mono (hcd : c ≤ d) {p : Prog P Γ σ}
    (h : mnNativePushBound c p) : mnNativePushBound d p := by
  induction p with
  | act a => exact h.trans hcd
  | seq p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | cond b p q hp hq => exact ⟨hp h.1,hq h.2⟩
  | loop b p hp => exact hp h
  | call f => exact h.elim

end IntegerMultBounds.MathlibTM2.Fast.Main
