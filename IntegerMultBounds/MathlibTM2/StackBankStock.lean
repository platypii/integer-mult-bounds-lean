module

public import IntegerMultBounds.MathlibTM2.StackResources

/-! Account for growth on a selected set of stacks through recursive executions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.MathlibTM2.Stack
variable {K' : Type} {Γ : K' → Type} {σ' P' : Type} [DecidableEq K']

def bankStock (bank : Finset K') (s : Store Γ σ') : ℕ := ∑ k ∈ bank, (s.stk k).length

def bankActPush (bank : Finset K') : Action Γ σ' → ℕ
  | .done => 0
  | .push k _ a => bankActPush bank a + (if k ∈ bank then 1 else 0)
  | .peek _ _ a | .pop _ _ a | .load _ a => bankActPush bank a
  | .branch _ a b => max (bankActPush bank a) (bankActPush bank b)

/-- Maximum pushes to the selected stacks by one action of the program. -/
def bankProgPush (bank : Finset K') : Prog P' Γ σ' → ℕ
  | .act a => bankActPush bank a
  | .seq p q | .cond _ p q => max (bankProgPush bank p) (bankProgPush bank q)
  | .loop _ p => bankProgPush bank p
  | .call _ => 0

/-- A native push bound also bounds pushes into any selected bank. -/
theorem bankProgPush_of_native (bank : Finset K') {p : Prog P' Γ σ'} {c : ℕ}
    (bound : mnNativePushBound c p) : bankProgPush bank p ≤ c := by
  have act (a : Action Γ σ') : bankActPush bank a ≤ mnActPush a := by
    induction a with
    | done => exact le_rfl
    | push k _ _ ih =>
      exact Nat.add_le_add ih (by split <;> decide)
    | branch _ _ _ ih₁ ih₂ => exact max_le_max ih₁ ih₂
    | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  induction p with
  | act a => exact (act a).trans bound
  | seq _ _ ih₁ ih₂ | cond _ _ _ ih₁ ih₂ => exact max_le (ih₁ bound.1) (ih₂ bound.2)
  | loop _ _ ih => exact ih bound
  | call _ => exact False.elim bound

private theorem bank_update (bank : Finset K') (s : Store Γ σ') (v : σ') (k : K') (word : List (Γ k)) :
    bankStock bank (⟨v,Function.update s.stk k word⟩ : Store Γ σ') + (if k ∈ bank then (s.stk k).length else 0) =
      bankStock bank s + (if k ∈ bank then word.length else 0) := by
  classical
  unfold bankStock
  have eq : (fun j => (Function.update s.stk k word j).length) =
      Function.update (fun j => (s.stk j).length) k word.length := by
    funext j
    by_cases h : j = k
    · subst j; simp
    · simp [Function.update_of_ne h]
  change (∑ j ∈ bank, (Function.update s.stk k word j).length) + _ = _
  rw [eq]
  by_cases h : k ∈ bank
  · simp only [h,ite_true]
    rw [Finset.sum_update_of_mem h,← Finset.add_sum_erase bank _ h,Finset.sdiff_singleton_eq_erase]
    omega
  · simp [h,Finset.sum_update_of_notMem]

private theorem action_stock (bank : Finset K') (a : Action Γ σ') (s : Store Γ σ') :
    bankStock bank (a.run s) ≤ bankStock bank s + bankActPush bank a := by
  induction a generalizing s with
  | done => simp [Action.run, bankActPush]
  | push k f a ih =>
      have h1 := ih ⟨s.var, Function.update s.stk k (f s.var :: s.stk k)⟩
      have h2 := bank_update bank s s.var k (f s.var :: s.stk k)
      simp only [Action.run, bankActPush]
      simp only [List.length_cons] at h2
      split_ifs at h2 ⊢ <;> omega
  | peek k f a ih =>
      have h1 := ih ⟨f s.var (s.stk k).head?, s.stk⟩
      simp only [Action.run, bankActPush]
      exact h1
  | pop k f a ih =>
      have h1 := ih ⟨f s.var (s.stk k).head?, Function.update s.stk k (s.stk k).tail⟩
      have h2 := bank_update bank s (f s.var (s.stk k).head?) k (s.stk k).tail
      have h3 : (s.stk k).tail.length ≤ (s.stk k).length := by simp
      simp only [Action.run, bankActPush]
      split_ifs at h2 <;> omega
  | load f a ih =>
      have h1 := ih ⟨f s.var, s.stk⟩
      simp only [Action.run, bankActPush]
      exact h1
  | branch f a b iha ihb =>
      simp only [Action.run, bankActPush]
      split
      · exact (iha s).trans (by have := le_max_left (bankActPush bank a) (bankActPush bank b); omega)
      · exact (ihb s).trans (by have := le_max_right (bankActPush bank a) (bankActPush bank b); omega)

/-- A run adds at most the selected push bound times its step count to this bank. -/
theorem exec_stock (bank : Finset K') {body : P' → Prog P' Γ σ'} {p : Prog P' Γ σ'} {s t : Store Γ σ'} {m c : ℕ}
    (h : Exec body p s m t) (hp : bankProgPush bank p ≤ c) (hb : ∀ f, bankProgPush bank (body f) ≤ c) :
    bankStock bank t ≤ bankStock bank s + c * m := by
  induction h with
  | act a s =>
      have := action_stock bank a s
      simp only [bankProgPush] at hp
      nlinarith
  | seq _ _ ih₁ ih₂ =>
      simp only [bankProgPush, max_le_iff] at hp
      have h1 := ih₁ hp.1
      have h2 := ih₂ hp.2
      nlinarith
  | cond_true _ _ ih =>
      simp only [bankProgPush, max_le_iff] at hp
      have h1 := ih hp.1
      nlinarith
  | cond_false _ _ ih =>
      simp only [bankProgPush, max_le_iff] at hp
      have h1 := ih hp.2
      nlinarith
  | loop_false _ => nlinarith
  | loop_true _ _ _ ih₁ ih₂ =>
      have h1 := ih₁ (by simpa only [bankProgPush] using hp)
      have h2 := ih₂ hp
      nlinarith
  | @call f _ _ _ _ ih =>
      have h1 := ih (hb f)
      nlinarith

end IntegerMultBounds.MathlibTM2.Fast.Main
