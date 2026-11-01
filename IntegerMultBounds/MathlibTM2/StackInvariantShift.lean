module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Reuse an execution trace at a larger ambient call depth. This changes only
its resource accounting, not its program, execution time or endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K]

theorem ExecWithin.shift {body : P → Prog P Γ σ} {Inv J : ℕ → Store Γ σ → Prop}
    {d n : ℕ} {p : Prog P Γ σ} {s t : Store Γ σ}
    (h : ExecWithin body Inv d p s n t) (δ : ℕ)
    (hIJ : ∀ r z, Inv r z → J (r+δ) z) : ExecWithin body J (d+δ) p s n t := by
  induction h with
  | act a s hi ho => exact .act a s (hIJ _ _ hi) (hIJ _ _ ho)
  | seq _ _ hp hq => exact .seq hp hq
  | cond_true hf _ hp => exact .cond_true hf hp
  | cond_false hf _ hp => exact .cond_false hf hp
  | loop_false hf hi => exact .loop_false hf (hIJ _ _ hi)
  | loop_true hf _ _ hp hq => exact .loop_true hf hp hq
  | call hi _ ho hp =>
    exact .call (hIJ _ _ hi) (by simpa only [Nat.add_right_comm] using hp) (hIJ _ _ ho)

end IntegerMultBounds.MathlibTM2.Stack

namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K] [Fintype K]

theorem mn_exec_within_shift {body : P → Prog P Γ σ} {d B n : ℕ}
    {p : Prog P Γ σ} {s t : Store Γ σ}
    (h : ExecWithin body (fun r z => mnSize z+r ≤ B) d p s n t) (δ : ℕ) :
    ExecWithin body (fun r z => mnSize z+r ≤ B+δ) (d+δ) p s n t := by
  exact h.shift δ (by intro r z hz; omega)

end IntegerMultBounds.MathlibTM2.Fast.Main
