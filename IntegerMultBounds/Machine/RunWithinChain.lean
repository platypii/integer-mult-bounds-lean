module

public import IntegerMultBounds.Machine.RunWithin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Structural composition of bounded runs with boundary shapes. Workspace is
shared, while the optional runtime bounds add. -/
@[expose] public section
namespace IntegerMultBounds.Machine.RunWithin
variable {β : Type} {t q a : ℕ} {M : Program t q a}

theorem chain (cfg : ℕ → β → Config t q a) (P : ℕ → β → Prop) (H : TapePred t a)
    (y₀ : β) (h₀ : P 0 y₀) (hsafe : H (cfg 0 y₀).tapes) :
    ∀ N, (∀ i < N, ∀ y, P i y → ∃ y', P (i+1) y' ∧
      ∃ n, RunWithin M H n (cfg i y) (cfg (i+1) y')) →
      ∃ y, P N y ∧ ∃ n, RunWithin M H n (cfg 0 y₀) (cfg N y)
  | 0, _ => ⟨y₀,h₀,0,RunWithin.refl hsafe⟩
  | N+1, h => by
    obtain ⟨y,hy,n,hr⟩ := chain cfg P H y₀ h₀ hsafe N (fun i hi => h i (by omega))
    obtain ⟨y',hy',m,hs⟩ := h N (by omega) y hy
    exact ⟨y',hy',n+m,hr.trans hs⟩

theorem chain_cost (cfg : ℕ → β → Config t q a) (P : ℕ → β → Prop) (H : TapePred t a)
    (cost : ℕ → ℕ) (y₀ : β) (h₀ : P 0 y₀) (hsafe : H (cfg 0 y₀).tapes) :
    ∀ N, (∀ i < N, ∀ y, P i y → ∃ y', P (i+1) y' ∧
      ∃ n ≤ cost i, RunWithin M H n (cfg i y) (cfg (i+1) y')) →
      ∃ y, P N y ∧ ∃ n ≤ ∑ i ∈ Finset.range N, cost i,
        RunWithin M H n (cfg 0 y₀) (cfg N y)
  | 0, _ => ⟨y₀,h₀,0,by simp,RunWithin.refl hsafe⟩
  | N+1, h => by
    obtain ⟨y,hy,n,hn,hr⟩ := chain_cost cfg P H cost y₀ h₀ hsafe N (fun i hi => h i (by omega))
    obtain ⟨y',hy',m,hm,hs⟩ := h N (by omega) y hy
    exact ⟨y',hy',n+m,by rw [Finset.sum_range_succ]; omega,hr.trans hs⟩

end IntegerMultBounds.Machine.RunWithin
