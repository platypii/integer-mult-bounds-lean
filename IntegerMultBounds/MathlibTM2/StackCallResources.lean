module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Trace bounds for bounded setup work, including procedure calls and return
 depth. Repeated arithmetic needs a separate workspace bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack

variable {K : Type} {Γ : K → Type} {σ P : Type}
  [DecidableEq K] [Fintype K]

/-- Every intermediate store and outstanding return frame is charged. The
extra unit per step covers return depth even when atomic actions push nothing. -/
theorem mn_exec_within {body : P → Prog P Γ σ} {p : Prog P Γ σ}
    {s t : Store Γ σ} {steps c : ℕ} (he : Exec body p s steps t)
    (hp : mnProgPush p ≤ c) (hb : ∀ f, mnProgPush (body f) ≤ c) :
    ∀ d B, mnSize s+d+(c+1)*steps ≤ B →
      ExecWithin body (fun depth z => mnSize z+depth ≤ B) d p s steps t := by
  induction he with
  | act a s =>
    intro d B hB
    have ha := mn_act_size a s
    change mnActPush a ≤ c at hp
    exact .act a s (by omega) (by omega)
  | @seq p q s t u m n h₁ h₂ ih₁ ih₂ =>
    intro d B hB
    obtain ⟨hp,hq⟩ := max_le_iff.mp hp
    have ht := mn_exec_size h₁ hp hb
    exact .seq (ih₁ hp d B (by nlinarith)) (ih₂ hq d B (by nlinarith))
  | @cond_true f p q s t n hf _ ih =>
    intro d B hB
    exact .cond_true hf (ih (max_le_iff.mp hp).1 d B (by nlinarith))
  | @cond_false f p q s t n hf _ ih =>
    intro d B hB
    exact .cond_false hf (ih (max_le_iff.mp hp).2 d B (by nlinarith))
  | loop_false hf =>
    intro d B hB
    exact .loop_false hf (by omega)
  | @loop_true f p s t u m n hf h₁ _ ih₁ ih₂ =>
    intro d B hB
    have ht := mn_exec_size h₁ hp hb
    exact .loop_true hf (ih₁ hp d B (by nlinarith)) (ih₂ hp d B (by nlinarith))
  | @call f s t n he ih =>
    intro d B hB
    have ht := mn_exec_size he (hb f) hb
    exact .call (by omega) (ih (hb f) (d+1) B (by nlinarith)) (by nlinarith)

/-- Finite procedure tables have a fixed push constant, independent of input
sizes and the number of recursive calls. -/
theorem mn_exec_finite_within [Fintype P] {body : P → Prog P Γ σ}
    {p : Prog P Γ σ} {s t : Store Γ σ} {steps budget depth : ℕ}
    (he : Exec body p s steps t) (hsteps : steps ≤ budget) :
    ExecWithin body (fun d z => mnSize z+d ≤
      mnSize s+depth+(max (mnProgPush p) (mnPushC body)+1)*budget)
      depth p s steps t := by
  apply mn_exec_within he (le_max_left _ _)
    (fun f => (mn_progPush_le_pushC body f).trans (le_max_right _ _))
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hsteps) _

end IntegerMultBounds.MathlibTM2.Fast.Main
