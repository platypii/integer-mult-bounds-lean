module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBRunStock
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock
public import IntegerMultBounds.MathlibTM2.Host.BankGrowth

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

/-- Growing archive roles may be balanced by shrinking input roles. Account
only for the finite changed bank; all other roles and spectators are framed. -/
theorem RsbHolds.size_le_of_bank_growth {N T Q A growth : ℕ} {U R : Type} {rg : R → Fin T}
    {ρ σ : R → List (Fin (A+4))} {S F : Stacks T A}
    (hrg : Function.Injective rg) (roles : Fin N → R) (hroles : Function.Injective roles)
    (hS : RsbHolds rg S ρ) (hF : RsbHolds rg F σ) (hf : RsbFr rg S F)
    (hframe : ∀ r, (∀ i, roles i ≠ r) → σ r = ρ r)
    (hlen : (∑ i, (σ (roles i)).length) ≤ (∑ i, (ρ (roles i)).length)+growth)
    (v w : HS T Q A U) : mnSize (mk w F) ≤ mnSize (mk v S)+growth := by
  classical
  have h := mn_replace_bank_size (rg ∘ roles) (hrg.comp hroles) v w S F
    (fun i => σ (roles i)) (fun i => hF (roles i)) (by
      intro k hk
      by_cases hr : ∃ r, rg r = k
      · obtain ⟨r,rfl⟩ := hr
        rw [hF r,hS r]
        exact hframe r (fun i hi => hk i (congrArg rg hi))
      · exact hf.2.2.2 k (by simpa only [not_exists] using hr)) hf.1 hf.2.1 hf.2.2.1
  simp only [Function.comp_apply] at h
  have hbefore : (∑ i, (S.R (rg (roles i))).length) = ∑ i, (ρ (roles i)).length := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hS (roles i)]
  rw [hbefore] at h
  omega

theorem RsbHolds.size_le_of_bank {N T Q A : ℕ} {U R : Type} {rg : R → Fin T}
    {ρ σ : R → List (Fin (A+4))} {S F : Stacks T A}
    (hrg : Function.Injective rg) (roles : Fin N → R) (hroles : Function.Injective roles)
    (hS : RsbHolds rg S ρ) (hF : RsbHolds rg F σ) (hf : RsbFr rg S F)
    (hframe : ∀ r, (∀ i, roles i ≠ r) → σ r = ρ r)
    (hlen : (∑ i, (σ (roles i)).length) ≤ ∑ i, (ρ (roles i)).length)
    (v w : HS T Q A U) : mnSize (mk w F) ≤ mnSize (mk v S) := by
  simpa using RsbHolds.size_le_of_bank_growth (growth := 0) hrg roles hroles hS hF hf
    hframe (by simpa using hlen) v w

end IntegerMultBounds.MathlibTM2.Fast
