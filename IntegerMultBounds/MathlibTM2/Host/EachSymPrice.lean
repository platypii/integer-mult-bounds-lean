module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Variable-price execution of the existing symbol loop. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {T Q A : ℕ} {U P : Type} (body : P → Pr P T Q A U)

def symLoopPrice (price : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, j => price j + 3 + symLoopPrice price n (j + 1)

/-- Doubling growth pays for all earlier unary scans by a telescoping potential. -/
theorem symLoopPrice_le_doubling (size : ℕ → ℕ) (n j : ℕ)
    (hgrowth : ∀ k, j ≤ k → k < j + n → 2 * size k ≤ size (k + 1)) :
    symLoopPrice (fun k => 4 * size k + 6) n j + 4 * size j ≤
      4 * size (j + n) + 9 * n + 1 := by
  induction n generalizing j with
  | zero => simp [symLoopPrice, Nat.add_comm]
  | succ n ih =>
    have h := ih (j + 1) (fun k hk hkn => hgrowth k (by omega) (by omega))
    have hg := hgrowth j le_rfl (by omega)
    rw [show j + 1 + n = j + (n + 1) by omega] at h
    simp only [symLoopPrice]
    omega

def PricedSymSpec (p : Pr P T Q A U) (a t : Fin T) (l : List (Fin (A + 4))) (Ψ : ℕ → Regs T A)
    (price : ℕ → ℕ) : Prop :=
  ∀ j (hj : j < l.length) (v : HS T Q A U) (S : Stacks T A), v.sym = some l[j] →
    (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) →
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ price j ∧
      Exec body p (mk v S) m (mk v' { S with R := R' }) ∧ R' a = S.R a ∧ R' t = S.R t ∧
      ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + 1) k

theorem eachSym_priced_loop {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U} {l : List (Fin (A + 4))}
    {Ψ : ℕ → Regs T A} {price : ℕ → ℕ} (hp : PricedSymSpec body p a t l Ψ price) :
    ∀ (n j : ℕ) (v : HS T Q A U) (S : Stacks T A), j + n = l.length → S.R a = l.drop j →
      (∀ k, k ≠ a → k ≠ t → S.R k = Ψ j k) → v.flag = (S.R a).head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧ m ≤ symLoopPrice price n j ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (mk v S) m (mk v' { S with R := R' }) ∧
        R' a = [] ∧ R' t = (l.drop j).reverse ++ S.R t ∧
        ∀ k, k ≠ a → k ≠ t → R' k = Ψ (j + n) k
  | 0, j, v, S, hn, hS, hΨ, hfl => by
      have hd : l.drop j = [] := List.drop_eq_nil_of_le (by omega)
      rw [hd] at hS
      exact ⟨v, S.R, 1, rfl, by simp [symLoopPrice], .loop_false (by simpa [hS] using hfl), hS, by simp [hd],
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
      obtain ⟨v', R', m', hu', hm', he', ha', ht', hΨ'⟩ := eachSym_priced_loop hat hp n (j + 1)
        { v₁ with flag := (R₁ a).head?.isSome } { S with R := R₁ } (by omega) ha₁' hΨ₁ rfl
      refine ⟨v', R', 1 + (m₁ + 1) + m' + 1, by rw [hu', ← hu₁], ?_,
        Exec.loop_true (by show v.flag = true; rw [hfl, hS']; rfl) (Exec.seq (hrun ▸ Exec.act (body := body) _ (mk v S))
          (Exec.seq he₁ he₂)) he', ha', ?_, ?_⟩
      · dsimp only [symLoopPrice]; omega
      · rw [ht']; dsimp only
        rw [ht₁]; dsimp only
        rw [Function.update_self, List.drop_eq_getElem_cons hj, List.reverse_cons,
          List.append_assoc]
        rfl
      · intro k hka hkt
        rw [hΨ' k hka hkt, Nat.add_assoc, Nat.add_comm 1]


theorem eachSym_priced_exec {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U} {Ψ : ℕ → Regs T A} {price : ℕ → ℕ}
    (v : HS T Q A U) (S : Stacks T A) (hp : PricedSymSpec body p a t (S.R a) Ψ price)
    (hΨ : ∀ k, k ≠ a → k ≠ t → S.R k = Ψ 0 k) :
    ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧
      m ≤ 1 + symLoopPrice price (S.R a).length 0 ∧
      Exec body (eachSym a t p) (mk v S) m (mk v' { S with R := R' }) ∧
      R' a = [] ∧ R' t = (S.R a).reverse ++ S.R t ∧
      ∀ k, k ≠ a → k ≠ t → R' k = Ψ (S.R a).length k := by
  obtain ⟨v', R', m, hu, hm, he, ha', ht', hΨ'⟩ := eachSym_priced_loop body hat hp (S.R a).length 0
    { v with flag := (S.R a).head?.isSome } S (by simp) (by simp) hΨ rfl
  refine ⟨v', R', 1 + m, hu, by omega, Exec.seq (peekR_run a v S ▸
    Exec.act (body := body) (peekR a) (mk v S)) he, ha', by simpa using ht', ?_⟩
  simpa using hΨ'

end IntegerMultBounds.MathlibTM2.Host
