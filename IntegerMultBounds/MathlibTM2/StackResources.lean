module

public import IntegerMultBounds.MathlibTM2.Host.Core
public import IntegerMultBounds.MathlibTM2.StackInvariant
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Generic stack-volume and push bounds, shared by host kernels and the multiplier. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

section Push

variable {K' : Type} {Γ : K' → Type} {σ' : Type} {P' : Type}

/-- The largest number of symbols one run of an action pushes. -/
def mnActPush : Action Γ σ' → ℕ
  | .done => 0
  | .push _ _ a => mnActPush a + 1
  | .peek _ _ a => mnActPush a
  | .pop _ _ a => mnActPush a
  | .load _ a => mnActPush a
  | .branch _ a b => max (mnActPush a) (mnActPush b)

/-- The largest push count of the actions of a program (calls excluded). -/
def mnProgPush : Prog P' Γ σ' → ℕ
  | .act a => mnActPush a
  | .seq p q => max (mnProgPush p) (mnProgPush q)
  | .cond _ p q => max (mnProgPush p) (mnProgPush q)
  | .loop _ p => mnProgPush p
  | .call _ => 0

/-- The largest push count of the actions of a procedure table. -/
def mnPushC [Fintype P'] (body : P' → Prog P' Γ σ') : ℕ :=
  Finset.univ.sup fun f => mnProgPush (body f)

/-- A call-free program whose atomic actions push at most `c` symbols. -/
def mnNativePushBound (c : ℕ) : Prog P' Γ σ' → Prop
  | .act a => mnActPush a ≤ c
  | .seq p q => mnNativePushBound c p ∧ mnNativePushBound c q
  | .cond _ p q => mnNativePushBound c p ∧ mnNativePushBound c q
  | .loop _ p => mnNativePushBound c p
  | .call _ => False

end Push

section Size

variable {K' : Type} {Γ : K' → Type} {σ' P' : Type}

/-- The total number of symbols on the stacks of a store. -/
def mnSize [Fintype K'] (s : Store Γ σ') : ℕ := ∑ k, (s.stk k).length

variable [DecidableEq K'] [Fintype K']

/-- The size after replacing one stack. -/
lemma mn_size_update (s : Store Γ σ') (v : σ') (k : K') (l : List (Γ k)) :
    mnSize (⟨v, Function.update s.stk k l⟩ : Store Γ σ') + (s.stk k).length =
      mnSize s + l.length := by
  unfold mnSize
  have e : (fun j => (Function.update s.stk k l j).length) =
      Function.update (fun j => (s.stk j).length) k l.length := by
    funext j
    by_cases h : j = k
    · subst h; simp
    · simp [Function.update_of_ne h]
  simp only
  rw [e, Finset.sum_update_of_mem (Finset.mem_univ k)]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
  rw [Finset.sdiff_singleton_eq_erase]
  ring

/-- One run of an action pushes at most `mnActPush a` symbols. -/
theorem mn_act_size (a : Action Γ σ') (s : Store Γ σ') :
    mnSize (a.run s) ≤ mnSize s + mnActPush a := by
  induction a generalizing s with
  | done => simp [Action.run, mnActPush]
  | push k f a ih =>
      have h1 := ih ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
      have h2 := mn_size_update s s.var k (f s.var :: s.stk k)
      simp only [Action.run, mnActPush]
      simp only [List.length_cons] at h2
      omega
  | peek k f a ih =>
      have h1 := ih ⟨f s.var (s.stk k).head?, s.stk⟩
      simp only [Action.run, mnActPush]
      exact h1
  | pop k f a ih =>
      have h1 := ih ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
      have h2 := mn_size_update s (f s.var (s.stk k).head?) k (s.stk k).tail
      have h3 : (s.stk k).tail.length ≤ (s.stk k).length := by simp
      simp only [Action.run, mnActPush]
      omega
  | load f a ih =>
      have h1 := ih ⟨f s.var, s.stk⟩
      simp only [Action.run, mnActPush]
      exact h1
  | branch f a b iha ihb =>
      simp only [Action.run, mnActPush]
      split
      · exact (iha s).trans (by have := le_max_left (mnActPush a) (mnActPush b); omega)
      · exact (ihb s).trans (by have := le_max_right (mnActPush a) (mnActPush b); omega)

/-- **Sizes along an execution.** If every action of the program and of the procedure bodies
pushes at most `c` symbols, an execution of `m` steps adds at most `c m` symbols. -/
theorem mn_exec_size {body : P' → Prog P' Γ σ'} {p : Prog P' Γ σ'} {s t : Store Γ σ'} {m c : ℕ}
    (h : Exec body p s m t) (hp : mnProgPush p ≤ c) (hb : ∀ f, mnProgPush (body f) ≤ c) :
    mnSize t ≤ mnSize s + c * m := by
  induction h with
  | act a s =>
      have := mn_act_size a s
      simp only [mnProgPush] at hp
      nlinarith
  | seq _ _ ih₁ ih₂ =>
      simp only [mnProgPush, max_le_iff] at hp
      have h1 := ih₁ hp.1
      have h2 := ih₂ hp.2
      nlinarith
  | cond_true _ _ ih =>
      simp only [mnProgPush, max_le_iff] at hp
      have h1 := ih hp.1
      nlinarith
  | cond_false _ _ ih =>
      simp only [mnProgPush, max_le_iff] at hp
      have h1 := ih hp.2
      nlinarith
  | loop_false _ => nlinarith
  | loop_true _ _ _ ih₁ ih₂ =>
      have h1 := ih₁ (by simpa only [mnProgPush] using hp)
      have h2 := ih₂ hp
      nlinarith
  | @call f _ _ _ _ ih =>
      have h1 := ih (hb f)
      nlinarith

omit [DecidableEq K'] [Fintype K'] in
/-- `mnPushC body` bounds the push count of every procedure body. -/
theorem mn_progPush_le_pushC [Fintype P'] (body : P' → Prog P' Γ σ') (f : P') :
    mnProgPush (body f) ≤ mnPushC body :=
  Finset.le_sup (f := fun f => mnProgPush (body f)) (Finset.mem_univ f)

/-- For native kernels, a linear time bound also certifies every intermediate stack volume.
This is intended for linear stream work, not as a replacement for arithmetic workspace bounds. -/
theorem mn_native_exec_within {body : P' → Prog P' Γ σ'} {p : Prog P' Γ σ'}
    {s t : Store Γ σ'} {steps : ℕ} (h : Exec body p s steps t) :
    ∀ c, mnNativePushBound c p → ∀ d B, mnSize s+d+c*steps ≤ B →
      ExecWithin body (fun depth z => mnSize z+depth ≤ B) d p s steps t := by
  induction h with
  | act a s =>
    intro c hp d B hB
    have ha := mn_act_size a s
    change mnActPush a ≤ c at hp
    exact .act a s (by omega) (by omega)
  | @seq p q s t u m n h₁ h₂ ih₁ ih₂ =>
    intro c hp d B hB
    obtain ⟨hp,hq⟩ := hp
    have ht := (ih₁ c hp d (mnSize s+d+c*m) le_rfl).final
    have hfirst : mnSize s+d+c*m ≤ B := by nlinarith only [hB,Nat.zero_le (c*n)]
    have hnext : mnSize t+d+c*n ≤ B := by nlinarith only [hB,ht]
    exact .seq (ih₁ c hp d B hfirst) (ih₂ c hq d B hnext)
  | @cond_true f p q s t n hf _ ih =>
    intro c hp d B hB
    have hn : mnSize s+d+c*n ≤ B := by nlinarith only [hB,Nat.zero_le c]
    exact .cond_true hf (ih c hp.1 d B hn)
  | @cond_false f p q s t n hf _ ih =>
    intro c hp d B hB
    have hn : mnSize s+d+c*n ≤ B := by nlinarith only [hB,Nat.zero_le c]
    exact .cond_false hf (ih c hp.2 d B hn)
  | loop_false hf =>
    intro c hp d B hB
    exact .loop_false hf (by omega)
  | @loop_true f p s t u m n hf _ _ ih₁ ih₂ =>
    intro c hp d B hB
    have ht := (ih₁ c hp d (mnSize s+d+c*m) le_rfl).final
    have hfirst : mnSize s+d+c*m ≤ B := by nlinarith only [hB,Nat.zero_le (c*n),Nat.zero_le c]
    have hnext : mnSize t+d+c*n ≤ B := by nlinarith only [hB,ht,Nat.zero_le c]
    exact .loop_true hf (ih₁ c hp d B hfirst) (ih₂ c hp d B hnext)
  | call _ _ =>
    intro c hp
    exact False.elim hp

end Size

/-! ### Host stores -/

section Host

variable {T Q A : ℕ} {U : Type}

/-- The registers of a host store hold at most `mnSize` symbols. -/
theorem mn_sumR_le_size (v : HS T Q A U) (S : Stacks T A) :
    ∑ i, (S.R i).length ≤ mnSize (mk v S) := by
  unfold mnSize
  have e : ∑ i, (S.R i).length = ∑ k ∈ Finset.univ.map ⟨HK.rt, fun _ _ h => HK.rt.inj h⟩,
      ((mk v S).stk k).length := by
    rw [Finset.sum_map]
    rfl
  rw [e]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end Host

end IntegerMultBounds.MathlibTM2.Fast.Main
