module

public import IntegerMultBounds.MathlibTM2.StackCallResources

/-! Reuse one middle-phase stock certificate between bounded setup and release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K] [Fintype K]

/-- A proved time bound supplies a resource certificate for bounded one-time work. -/
theorem mn_bounded_exec_certify {body : P → Prog P Γ σ} {p : Prog P Γ σ}
    {s t : Store Γ σ} {steps budget : ℕ} (he : Exec body p s steps t) (ht : steps ≤ budget) :
    ∀ C, mnProgPush p ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(C+1)*budget) depth p s steps t := by
  intro C hp hb depth
  apply mn_exec_within he hp hb depth
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ ht) _

/-- Resource certificates stack by adding their allowances, not their running times. -/
theorem mn_seq_exec_within {body : P → Prog P Γ σ} {p q : Prog P Γ σ}
    {s t u : Store Γ σ} {m n firstCost secondCost : ℕ}
    (hp : ∀ C, mnProgPush p ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(C+1)*firstCost) depth p s m t)
    (hq : ∀ C, mnProgPush q ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize t+depth+(C+1)*secondCost) depth q t n u) :
    ∀ C, mnProgPush (.seq p q) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(C+1)*(firstCost+secondCost))
        depth (.seq p q) s (m+n) u := by
  intro C hpush hb depth
  obtain ⟨hpushp,hpushq⟩ := max_le_iff.mp hpush
  have hsize : mnSize t+0 ≤ mnSize s+0+(C+1)*firstCost := (hp C hpushp hb 0).final
  simp only [Nat.add_zero] at hsize
  refine .seq ((hp C hpushp hb depth).mono ?_) ((hq C hpushq hb depth).mono ?_)
  · intro d z hz
    nlinarith only [hz]
  · intro d z hz
    nlinarith only [hz,hsize]

/-- Compose bounded setup with a live phase while charging persistent data
once, outside the per-step workspace multiplier. -/
theorem mn_setup_exec_within_stock {body : P → Prog P Γ σ} {p q : Prog P Γ σ}
    {s t u : Store Γ σ} {m n setup persistent scratch C depth : ℕ}
    (he : Exec body p s m t) (hm : m ≤ setup)
    (hp : mnProgPush p ≤ C) (hb : ∀ f, mnProgPush (body f) ≤ C)
    (hq : ExecWithin body (fun d z => mnSize z+d ≤ mnSize t+persistent+depth+(C+1)*scratch)
      depth q t n u) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+persistent+depth+(C+1)*(setup+scratch))
      depth (.seq p q) s (m+n) u := by
  have hsetup := mn_bounded_exec_certify he hm C hp hb depth
  have hfinal := hsetup.final
  refine .seq (hsetup.mono ?_) (hq.mono ?_)
  · intro d z hz
    nlinarith only [hz]
  · intro d z hz
    nlinarith only [hz,hfinal]

/-- Append bounded release work to a live certificate while retaining the
single persistent-data charge. -/
theorem mn_release_exec_within_stock {body : P → Prog P Γ σ} {p q : Prog P Γ σ}
    {s t u : Store Γ σ} {m n work persistent release C depth : ℕ}
    (hwork : ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+persistent+depth+(C+1)*work)
      depth p s m t)
    (he : Exec body q t n u) (hn : n ≤ release)
    (hq : mnProgPush q ≤ C) (hb : ∀ f, mnProgPush (body f) ≤ C) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+persistent+depth+(C+1)*(work+release))
      depth (.seq p q) s (m+n) u := by
  have hfinal := hwork.final
  refine .seq (hwork.mono ?_) ?_
  · intro d z hz
    nlinarith only [hz]
  · apply mn_exec_within he hq hb depth
    have hm := Nat.mul_le_mul_left (C+1) hn
    nlinarith only [hfinal,hm]

/-- Setup, live work and release share one stock budget. No middle-phase time
bound is substituted for its already proved resource certificate. -/
theorem mn_lifecycle_exec_within {body : P → Prog P Γ σ} {p q r : Prog P Γ σ}
    {s t u v : Store Γ σ} {m n k setup work release : ℕ}
    (he : Exec body p s m t) (hm : m ≤ setup)
    (hwork : ∀ C, mnProgPush q ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize t+depth+(C+1)*work) depth q t n u)
    (hf : Exec body r u k v) (hk : k ≤ release) :
    ∀ C, mnProgPush (.seq p (.seq q r)) ≤ C → (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(C+1)*(setup+work+release))
        depth (.seq p (.seq q r)) s (m+(n+k)) v := by
  have hw := mn_seq_exec_within (mn_bounded_exec_certify he hm)
    (mn_seq_exec_within hwork (mn_bounded_exec_certify hf hk))
  simpa only [Nat.add_assoc] using hw

end IntegerMultBounds.MathlibTM2.Fast.Main
