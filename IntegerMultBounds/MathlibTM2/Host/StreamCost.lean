module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Variable iteration costs for the existing counted stream loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

def symbolCost (c : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => c j+symbolCost c (j+1) n

theorem symbolCost_eq_sum_list (c : ℕ → ℕ) (j : ℕ) (xs : List ℕ)
    (hc : ∀ i (hi : i < xs.length), c (j+i) = xs[i]) :
    symbolCost c j xs.length = xs.sum := by
  induction xs generalizing j with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons,symbolCost,List.sum_cons]
    have hh := hc 0 (by simp)
    simp only [Nat.add_zero,List.getElem_cons_zero] at hh
    rw [hh,ih (j+1) (by
      intro i hi
      have ht := hc (i+1) (by simpa using Nat.succ_lt_succ hi)
      change c (j+(i+1)) = xs[i] at ht
      rw [show j+1+i = j+(i+1) by omega]
      exact ht)]

def SymCostSpec (p : Pr P T Q A U) (a t : Fin T) (l : List (Fin (A + 4))) (Ψ : ℕ → Regs T A)
    (c : ℕ → ℕ) : Prop :=
  ∀ j (hj : j < l.length) (v : HS T Q A U) (S : Stacks T A), v.sym = some l[j] →
    (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) →
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ c j ∧
      Exec body p (mk v S) m (mk v' { S with R := R' }) ∧ R' a = S.R a ∧ R' t = S.R t ∧
      ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + 1) k

theorem eachSym_cost_loop {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U} {l : List (Fin (A + 4))}
    {Ψ : ℕ → Regs T A} {c : ℕ → ℕ} (hp : SymCostSpec body p a t l Ψ c) :
    ∀ (n j : ℕ) (v : HS T Q A U) (S : Stacks T A), j + n = l.length → S.R a = l.drop j →
      (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) → v.flag = (S.R a).head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ symbolCost c j n + 3*n + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (mk v S) m (mk v' { S with R := R' }) ∧
        R' a = [] ∧ R' t = (l.drop j).reverse ++ S.R t ∧
        ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + n) k
  | 0, j, v, S, hn, hS, hΨ, hfl => by
      have hd : l.drop j = [] := List.drop_eq_nil_of_le (by omega)
      rw [hd] at hS
      exact ⟨v, S.R, 1, rfl, by simp [symbolCost], .loop_false (by simpa [hS] using hfl), hS, by simp [hd],
        by simpa using hΨ⟩
  | n + 1, j, v, S, hn, hS, hΨ, hfl => by
      have hj : j < l.length := by omega
      have hS' : S.R a = l[j] :: l.drop (j + 1) := by rw [hS, List.drop_eq_getElem_cons hj]
      have hrun : (popPush a t : Act T Q A U).run (mk v S) = mk { v with sym := some l[j] }
          { S with
            R := Function.update (Function.update S.R a (l.drop (j + 1))) t (l[j] :: S.R t) } := by
        simp only [popPush, Action.run, mk_var, mk_stk, get_rt, hS', List.head?_cons,
          List.tail_cons, Option.getD_some, update_rt, store_mk]
        rw [Function.update_of_ne hat.symm]
      obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, ha₁, ht₁, hΨ₁⟩ := hp j hj { v with sym := some l[j] }
        { S with
          R := Function.update (Function.update S.R a (l.drop (j + 1))) t (l[j] :: S.R t) } rfl
        (fun k hka hkt => by
          simpa [Function.update_of_ne hka, Function.update_of_ne hkt] using hΨ k hka hkt)
      have ha₁' : R₁ a = l.drop (j + 1) := by rw [ha₁]; simp [Function.update_of_ne hat]
      have he₂ := Exec.act (body := body) (peekR a) (mk v₁ { S with R := R₁ })
      rw [peekR_run] at he₂
      obtain ⟨v', R', m', hu', hm', he', ha', ht', hΨ'⟩ := eachSym_cost_loop hat hp n (j + 1)
        { v₁ with flag := (R₁ a).head?.isSome } { S with R := R₁ } (by omega) ha₁' hΨ₁ rfl
      refine ⟨v', R', 1 + (m₁ + 1) + m' + 1, by rw [hu', ← hu₁], ?_,
        Exec.loop_true (by show v.flag = true; rw [hfl, hS']; rfl) (Exec.seq (hrun ▸ Exec.act (body := body) _ (mk v S))
          (Exec.seq he₁ he₂)) he', ha', ?_, ?_⟩
      · simp only [symbolCost]; omega
      · rw [ht']; dsimp only
        rw [ht₁]; dsimp only
        rw [Function.update_self, List.drop_eq_getElem_cons hj, List.reverse_cons,
          List.append_assoc]
        rfl
      · intro k hka hkt
        rw [hΨ' k hka hkt, Nat.add_assoc, Nat.add_comm 1]

/-- Sum individual iteration budgets instead of multiplying their maximum. -/
theorem eachSym_cost_exec {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U} {Ψ : ℕ → Regs T A} {c : ℕ → ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hp : SymCostSpec body p a t (S.R a) Ψ c)
    (hΨ : ∀ k, k ≠ a → k ≠ t → S.R k = Ψ 0 k) :
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧
      m ≤ symbolCost c 0 (S.R a).length + 3*(S.R a).length + 2 ∧
      Exec body (eachSym a t p) (mk v S) m (mk v' { S with R := R' }) ∧
      R' a = [] ∧ R' t = (S.R a).reverse ++ S.R t ∧
      ∀ k, k ≠ a → k ≠ t → R' k = Ψ (S.R a).length k := by
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := eachSym_cost_loop body hat hp (S.R a).length 0
    { v with flag := (S.R a).head?.isSome } S (by simp) (by simp) hΨ rfl
  refine ⟨v', R', 1 + m, hu, by omega, Exec.seq (peekR_run a v S ▸
    Exec.act (body := body) (peekR a) (mk v S)) he, ha', by simpa using ht', ?_⟩
  simpa using hΨ'


end IntegerMultBounds.MathlibTM2.Host
