module

public import IntegerMultBounds.MathlibTM2.StackInvariant
public import IntegerMultBounds.MathlibTM2.StackResources

/-! A verified trace may run beneath additional already outstanding calls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K]
  {body : P → Prog P Γ σ} {Inv J : ℕ → Store Γ σ → Prop}
  {d : ℕ} {p : Prog P Γ σ} {s t : Store Γ σ} {n : ℕ}

/-- Shift the call depth of a complete trace and transport its invariant. -/
theorem ExecWithin.add_depth (h : ExecWithin body Inv d p s n t) (k : ℕ)
    (hIJ : ∀ d s, Inv d s → J (d+k) s) : ExecWithin body J (d+k) p s n t := by
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
  {body : P → Prog P Γ σ} {p : Prog P Γ σ} {s t : Store Γ σ} {n work : ℕ}

/-- An additive stock certificate at depth zero works under any caller depth. -/
theorem mn_execWithin_add_depth
    (h : ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+0+work) 0 p s n t) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+work) depth p s n t := by
  simpa only [Nat.zero_add] using h.add_depth depth (J := fun d z => mnSize z+d ≤ mnSize s+depth+work)
    (by intro d z hz; omega)

end IntegerMultBounds.MathlibTM2.Fast.Main
