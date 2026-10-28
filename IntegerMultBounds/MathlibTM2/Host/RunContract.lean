module

public import IntegerMultBounds.MathlibTM2.Host.Stream

/-! Exact stack effects compose independently of host control state.
These contracts bound time; execution-wide storage requires a separate trace invariant. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- An exact stack transformation, uniformly in the initial host state. -/
def Runs (body : P → Pr P T Q A U) (p : Pr P T Q A U)
    (S S' : Stacks T A) (cost : ℕ) : Prop :=
  ∀ v : HS T Q A U, ∃ v' n, v'.user = v.user ∧ n ≤ cost ∧
    Exec body p (mk v S) n (mk v' S')

namespace Runs

theorem of_exact {p : Pr P T Q A U} {S S' : Stacks T A} {cost : ℕ}
    (h : ∀ v : HS T Q A U, ∃ v', v'.user = v.user ∧
      Exec body p (mk v S) cost (mk v' S')) : Runs body p S S' cost := by
  intro v
  obtain ⟨v',hu,he⟩ := h v
  exact ⟨v',cost,hu,le_rfl,he⟩

/-- Adapt a legacy execution/frame theorem to an exact stack effect. -/
theorem of_frame {p : Pr P T Q A U} {S : Stacks T A} {R : Fin T → List (Fin (A+4))} {cost : ℕ}
    (h : ∀ v : HS T Q A U, ∃ v' S' n, v'.user = v.user ∧ n ≤ cost ∧
      Exec body p (mk v S) n (mk v' S') ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧ S'.R = R) :
    Runs body p S {S with R := R} cost := by
  intro v
  obtain ⟨v',S',n,hu,hn,he,hi,ho,hl,hr⟩ := h v
  have hS' : S' = {S with R := R} := Stacks.ext hi ho hl hr
  exact ⟨v',n,hu,hn,hS' ▸ he⟩

theorem seq {p q : Pr P T Q A U} {S S₁ S₂ : Stacks T A} {c d : ℕ}
    (hp : Runs body p S S₁ c) (hq : Runs body q S₁ S₂ d) :
    Runs body (.seq p q) S S₂ (c+d) := by
  intro v
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := hp v
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hq v₁
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂⟩

theorem mono {p : Pr P T Q A U} {S S' : Stacks T A} {c d : ℕ}
    (h : Runs body p S S' c) (hcd : c ≤ d) : Runs body p S S' d := by
  intro v
  obtain ⟨v',n,hu,hn,he⟩ := h v
  exact ⟨v',n,hu,hn.trans hcd,he⟩

end Runs
end IntegerMultBounds.MathlibTM2.Host
