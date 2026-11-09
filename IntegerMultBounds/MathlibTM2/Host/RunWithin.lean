module

public import IntegerMultBounds.MathlibTM2.Host.RunContract
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Exact stack transformations with a separate additive workspace allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def RunsWithin (body : P → Pr P T Q A U) (p : Pr P T Q A U)
    (S F : Stacks T A) (cost work : ℕ) : Prop :=
  ∀ v : HS T Q A U, ∃ v' n, v'.user = v.user ∧ n ≤ cost ∧
    ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+work)
      depth p (mk v S) n (mk v' F)

namespace RunsWithin

theorem of_frame {p : Pr P T Q A U} {S : Stacks T A}
    {R : Fin T → List (Fin (A+4))} {cost work : ℕ}
    (h : ∀ v : HS T Q A U, ∃ v' F n, v'.user = v.user ∧ n ≤ cost ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+work)
        depth p (mk v S) n (mk v' F)) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧ F.R = R) :
    RunsWithin body p S {S with R := R} cost work := by
  intro v
  obtain ⟨v',F,n,hu,hn,he,hi,ho,hl,hr⟩ := h v
  have hF : F = {S with R := R} := Stacks.ext hi ho hl hr
  exact ⟨v',n,hu,hn,hF ▸ he⟩

theorem seq {p q : Pr P T Q A U} {S F G : Stacks T A} {c d a b : ℕ}
    (hp : RunsWithin body p S F c a) (hq : RunsWithin body q F G d b) :
    RunsWithin body (.seq p q) S G (c+d) (a+b) := by
  intro v
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := hp v
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := hq v₁
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,
    fun depth => mn_seq_within_add (he₁ depth) (he₂ depth)⟩

theorem mono {p : Pr P T Q A U} {S F : Stacks T A} {c d a b : ℕ}
    (h : RunsWithin body p S F c a) (hcd : c ≤ d) (hab : a ≤ b) :
    RunsWithin body p S F d b := by
  intro v
  obtain ⟨v',n,hu,hn,he⟩ := h v
  exact ⟨v',n,hu,hn.trans hcd,fun depth => (he depth).mono (by intro d z hz; omega)⟩

end RunsWithin

theorem Runs.native_within {p : Pr P T Q A U} {S F : Stacks T A} {cost K : ℕ}
    (h : Runs body p S F cost) (hnative : mnNativePushBound K p) :
    RunsWithin body p S F cost (K*cost) := by
  intro v
  obtain ⟨v',n,hu,hn,he⟩ := h v
  exact ⟨v',n,hu,hn,fun depth => mn_native_exec_within he K hnative depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left K hn) _)⟩

end IntegerMultBounds.MathlibTM2.Host
