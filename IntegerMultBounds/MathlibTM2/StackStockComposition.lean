module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Compose local additive workspace allowances on the same execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Stack
variable {K : Type} {Γ : K → Type} {σ P : Type} [DecidableEq K] [Fintype K]

theorem mn_seq_within_add {body : P → Prog P Γ σ} {p q : Prog P Γ σ}
    {s t u : Store Γ σ} {m n depth a b : ℕ}
    (hp : ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+a) depth p s m t)
    (hq : ExecWithin body (fun d z => mnSize z+d ≤ mnSize t+depth+b) depth q t n u) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(a+b))
      depth (.seq p q) s (m+n) u := by
  have ht := hp.final
  exact .seq (hp.mono (by intro d z hz; omega)) (hq.mono (by intro d z hz; omega))

end IntegerMultBounds.MathlibTM2.Fast.Main
