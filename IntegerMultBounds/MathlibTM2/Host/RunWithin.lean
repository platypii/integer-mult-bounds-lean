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

/-- Select the exact stack effect and reserve using the physical count register. -/
theorem branch {p q : Pr P T Q A U} {S Syes Sno : Stacks T A} {c d a b : ℕ} (count : Fin T)
    (hp : (S.R count).head?.isSome = true → RunsWithin body p S Syes c a)
    (hq : (S.R count).head?.isSome = false → RunsWithin body q S Sno d b) :
    RunsWithin body (.seq (.act (peekR count)) (.cond (·.flag) p q)) S
      (if (S.R count).head?.isSome then Syes else Sno)
      ((if (S.R count).head?.isSome then c else d)+2)
      (if (S.R count).head?.isSome then a else b) := by
  intro v
  have hpeek := Exec.act (body := body) (peekR count) (mk v S)
  rw [peekR_run] at hpeek
  have hn : mnNativePushBound 0 (.act (peekR count) : Pr P T Q A U) := by
    simp [peekR,mnNativePushBound,mnActPush]
  cases hb : (S.R count).head?.isSome with
  | false =>
    obtain ⟨v',n,hu,hm,he⟩ := hq hb {v with flag := false}
    refine ⟨v',1+(n+1),hu,?_,?_⟩
    · simp only [Bool.false_eq_true,↓reduceIte]; omega
    · intro depth
      rw [hb] at hpeek
      have ht := mn_native_exec_within hpeek 0 hn depth _ (Nat.le_refl _)
      simpa only [hb,Bool.false_eq_true,↓reduceIte,Nat.zero_mul,Nat.add_zero,Nat.zero_add]
        using mn_seq_within_add ht (ExecWithin.cond_false rfl (he depth))
  | true =>
    obtain ⟨v',n,hu,hm,he⟩ := hp hb {v with flag := true}
    refine ⟨v',1+(n+1),hu,?_,?_⟩
    · simp only [↓reduceIte]; omega
    · intro depth
      rw [hb] at hpeek
      have ht := mn_native_exec_within hpeek 0 hn depth _ (Nat.le_refl _)
      simpa only [hb,↓reduceIte,Nat.zero_mul,Nat.add_zero,Nat.zero_add]
        using mn_seq_within_add ht (ExecWithin.cond_true rfl (he depth))

end RunsWithin

theorem Runs.native_within {p : Pr P T Q A U} {S F : Stacks T A} {cost K : ℕ}
    (h : Runs body p S F cost) (hnative : mnNativePushBound K p) :
    RunsWithin body p S F cost (K*cost) := by
  intro v
  obtain ⟨v',n,hu,hn,he⟩ := h v
  exact ⟨v',n,hu,hn,fun depth => mn_native_exec_within he K hnative depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left K hn) _)⟩

end IntegerMultBounds.MathlibTM2.Host
