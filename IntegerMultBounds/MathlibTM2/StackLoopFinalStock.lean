module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Loops whose completed iterations only retain output reuse one native
scratch reserve. The reserve is added to final stock, not once per iteration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K] [Fintype K]

theorem loop_within_final_stock (body : P → Prog P Γ σ) (p : Prog P Γ σ)
    (test : σ → Bool) (I : Store Γ σ → Prop) (c cost : ℕ)
    (hnative : mnNativePushBound c p)
    (hstep : ∀ s t n, I s → test s.var = true → Exec body p s n t →
      I t ∧ n ≤ cost ∧ mnSize s ≤ mnSize t)
    {s t : Store Γ σ} {n : ℕ} (he : Exec body (.loop test p) s n t) (hs : I s) (depth : ℕ) :
    I t ∧ mnSize s ≤ mnSize t ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize t+depth+c*cost) depth (.loop test p) s n t := by
  induction n using Nat.strong_induction_on generalizing s t with
  | h n ih =>
    cases he with
    | loop_false hf => exact ⟨hs,le_rfl,.loop_false hf (by omega)⟩
    | @loop_true _ _ _ _ _ m k hf hp hq =>
      obtain ⟨hI,hm,hmono⟩ := hstep _ _ _ hs hf hp
      obtain ⟨hfinal,htail,hw⟩ := ih k (by omega) hq hI
      refine ⟨hfinal,hmono.trans htail,.loop_true hf ?_ hw⟩
      apply mn_native_exec_within hp c hnative depth
      have hmul := Nat.mul_le_mul_left c hm
      omega

end IntegerMultBounds.MathlibTM2.Fast.Main
