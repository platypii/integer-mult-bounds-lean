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
 /-- Phases measured from the same retained bank reuse their allowances. -/
theorem execWithin_seq_common_budget {body : P → Prog P Γ σ}
    {p q : Prog P Γ σ} {s t u : Store Γ σ} {m n base depth A B : ℕ}
    (hp : ExecWithin body (fun d z => mnSize z+d ≤ base+depth+A) depth p s m t)
    (hq : ExecWithin body (fun d z => mnSize z+d ≤ base+depth+B) depth q t n u) :
    ExecWithin body (fun d z => mnSize z+d ≤ base+depth+max A B) depth
      (.seq p q) s (m+n) u := by
  have hA := Nat.le_max_left A B
  have hB := Nat.le_max_right A B
  exact .seq (hp.mono (by intro d z hz; omega)) (hq.mono (by intro d z hz; omega))

end IntegerMultBounds.MathlibTM2.Host
