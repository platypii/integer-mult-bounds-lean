module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Sequential phases share storage; only their incremental allowances add. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
variable {K σ P : Type} {Γ : K → Type} [Fintype K] [DecidableEq K]

theorem execWithin_seq_two_budget (body : P → Prog P Γ σ)
    (p q : Prog P Γ σ) (s t u : Store Γ σ) (a b depth A B : ℕ)
    (hp : ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+A) depth p s a t)
    (hq : ExecWithin body (fun d z => mnSize z+d ≤ mnSize t+depth+B) depth q t b u) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize s+depth+(A+B)) depth
      (.seq p q) s (a+b) u := by
  have ht := hp.final
  apply ExecWithin.seq (hp.mono (by intro d z hz; omega))
  exact hq.mono (by intro d z hz; omega)


end IntegerMultBounds.MathlibTM2.Host
