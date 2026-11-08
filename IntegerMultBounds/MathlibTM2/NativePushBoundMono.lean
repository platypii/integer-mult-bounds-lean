module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Widen a call-free native push bound when composing kernels. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
variable {K σ P : Type} {Γ : K → Type}

theorem mnNativePushBound_mono {c d : ℕ} (hcd : c ≤ d) {p : Prog P Γ σ}
    (h : mnNativePushBound c p) : mnNativePushBound d p := by
  induction p with
  | act a => exact h.trans hcd
  | seq p q ihp ihq => exact ⟨ihp h.1,ihq h.2⟩
  | cond f p q ihp ihq => exact ⟨ihp h.1,ihq h.2⟩
  | loop f p ih => exact ih h
  | call f => exact h.elim

end IntegerMultBounds.MathlibTM2.Fast.Main
