module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBRunStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! A register valuation and its frame determine boundary stock. No enumeration
of register roles or concrete arithmetic values is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main

theorem RsbHolds.size_le_of_lengths {T Q A : ℕ} {U R : Type} {rg : R → Fin T}
    {ρ σ : R → List (Fin (A+4))} {S F : Stacks T A}
    (hS : RsbHolds rg S ρ) (hF : RsbHolds rg F σ) (hf : RsbFr rg S F)
    (hlen : ∀ r, (σ r).length ≤ (ρ r).length) (v w : HS T Q A U) :
    mnSize (mk w F) ≤ mnSize (mk v S) := by
  classical
  have hright (k : Fin T) : (F.R k).length ≤ (S.R k).length := by
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r,rfl⟩ := hk
      rw [hF r,hS r]
      exact hlen r
    · rw [hf.2.2.2 k (by simpa only [not_exists] using hk)]
  rw [mnSize_mk_registerBankStock,mnSize_mk_registerBankStock,hf.1,hf.2.1]
  apply Nat.add_le_add_left
  unfold registerBankStock
  apply Finset.sum_le_sum
  intro k _
  rw [congrFun hf.2.2.1 k]
  exact Nat.add_le_add_left (hright k) _

end IntegerMultBounds.MathlibTM2.Fast
