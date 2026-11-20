module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup

/-! Charge a record's workspace cleanup by total stack growth. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.MathlibTM2.Stack Host IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type}

private theorem update_stack_sum {K : Type} [DecidableEq K] (ks : List K) (distinct : ks.Nodup)
    (size : K → ℕ) (k : K) (n : ℕ) (extra : ℕ) (bound : n ≤ size k + extra) :
    (ks.map (Function.update size k n)).sum ≤ (ks.map size).sum + extra := by
  induction ks with
  | nil => simp
  | cons j ks ih =>
    by_cases eq : j = k
    · subst j
      have same : ks.map (Function.update size k n) = ks.map size := by
        apply List.map_congr_left
        intro i hi
        exact Function.update_of_ne (show i ≠ k by intro h; subst i; exact distinct.notMem hi) _ _
      simpa [same,Nat.add_right_comm] using Nat.add_le_add_right bound (ks.map size).sum
    · simp only [List.map_cons,List.sum_cons,Function.update_of_ne eq]
      have := ih distinct.tail
      omega

private theorem action_stack_sum {K σ : Type} {Γ : K → Type} [DecidableEq K]
    (ks : List K) (distinct : ks.Nodup) (a : Action Γ σ) (s : Store Γ σ) :
    (ks.map fun k => ((a.run s).stk k).length).sum ≤
      (ks.map fun k => (s.stk k).length).sum + mnActPush a := by
  induction a generalizing s with
  | done => simp [Action.run,mnActPush]
  | push k f a ih =>
    let t : Store Γ σ := ⟨s.var,Function.update s.stk k (f s.var :: s.stk k)⟩
    have lens : (fun j => (t.stk j).length) = Function.update (fun j => (s.stk j).length) k ((s.stk k).length+1) := by
      funext j; by_cases h : j = k
      · subst j; simp [t]
      · simp [t,h]
    have inc := update_stack_sum ks distinct (fun j => (s.stk j).length) k _ 1 le_rfl
    have h := ih t
    rw [← lens] at inc
    change _ ≤ _ + (mnActPush a + 1)
    exact h.trans (by omega)
  | pop k f a ih =>
    let t : Store Γ σ := ⟨f s.var (s.stk k).head?,Function.update s.stk k (s.stk k).tail⟩
    have lens : (fun j => (t.stk j).length) = Function.update (fun j => (s.stk j).length) k (s.stk k).tail.length := by
      funext j; by_cases h : j = k
      · subst j; simp [t]
      · simp [t,h]
    have dec := update_stack_sum ks distinct (fun j => (s.stk j).length) k _ 0
      (show (s.stk k).tail.length ≤ (s.stk k).length+0 by simp)
    rw [← lens] at dec
    exact (ih t).trans (Nat.add_le_add_right (by simpa only [Nat.add_zero] using dec) _)
  | peek k f a ih => exact ih _
  | load f a ih => exact ih _
  | branch f a b iha ihb =>
    simp only [Action.run,mnActPush]; split
    · exact (iha s).trans (Nat.add_le_add_left (le_max_left ..) _)
    · exact (ihb s).trans (Nat.add_le_add_left (le_max_right ..) _)

/-- Each push grows at most one of the selected stacks, independently of the
number of tapes the computation borrows. -/
theorem exec_stack_sum {K σ : Type} {Γ : K → Type} [DecidableEq K]
    {body : P → Prog P Γ σ} {p : Prog P Γ σ} {s t : Store Γ σ} {n c : ℕ}
    (ks : List K) (distinct : ks.Nodup) (run : Exec body p s n t)
    (hp : mnProgPush p ≤ c) (hb : ∀ f, mnProgPush (body f) ≤ c) :
    (ks.map fun k => (t.stk k).length).sum ≤ (ks.map fun k => (s.stk k).length).sum + c*n := by
  induction run with
  | act a s => exact (action_stack_sum ks distinct a s).trans (by simpa only [Nat.mul_one,mnProgPush] using Nat.add_le_add_left hp ((ks.map fun k => (s.stk k).length).sum))
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨h₁,h₂⟩ := max_le_iff.mp hp
    exact (ih₂ h₂).trans (by have := ih₁ h₁; rw [Nat.mul_add]; omega)
  | cond_true _ _ ih => have := ih (max_le_iff.mp hp).1; nlinarith
  | cond_false _ _ ih => have := ih (max_le_iff.mp hp).2; nlinarith
  | loop_false _ => simp
  | loop_true _ _ _ ih₁ ih₂ => have := ih₁ hp; have := ih₂ hp; nlinarith
  | @call f _ _ _ _ ih => have := ih (hb f); nlinarith

/-- Clearing distinct tapes costs their initial contents plus at most six
steps per pushed symbol, independent of the number of tapes. -/
theorem recordCleanup_cost_le (is : List (Fin T)) (distinct : is.Nodup)
    {body : P → Pr P T Q A U} {prog : Pr P T Q A U}
    {s t : HS T Q A U} {S F : Stacks T A} {n c : ℕ}
    (run : Exec body prog (mk s S) n (mk t F)) (hp : mnProgPush prog ≤ c)
    (hb : ∀ f, mnProgPush (body f) ≤ c) :
    (is.map fun i => 4*(F.L i).length+2*(F.R i).length+4).sum+1 ≤
      (is.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1 + 6*(c*n) := by
  have split (D : Stacks T A) : (is.map fun i => 4*(D.L i).length+2*(D.R i).length+4).sum =
      4*(is.map fun i => (D.L i).length).sum + 2*(is.map fun i => (D.R i).length).sum + 4*is.length := by
    clear distinct
    induction is with
    | nil => simp
    | cons i is ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.mul_add]; omega
  have side (k : Fin T → HK T) (inj : Function.Injective k) :=
    exec_stack_sum (is.map k) (distinct.map inj) run hp hb
  have left := side HK.lt (by intro i j h; injection h)
  have right := side HK.rt (by intro i j h; injection h)
  simp only [List.map_map,Function.comp_def,mk,get_lt,get_rt] at left right
  rw [split,split]
  omega

end IntegerMultBounds.MathlibTM2.Cover.Fallback
