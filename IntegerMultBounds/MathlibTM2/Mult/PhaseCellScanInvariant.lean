module

public import IntegerMultBounds.MathlibTM2.Node.Params

/-! Structural counted scanning with an invariant that may contain execution witnesses. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem scanInvariant_loop {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {Inv : ℕ → Regs T A → Prop} {c : ℕ → ℕ} {N : ℕ} {left : Regs T A}
    (hframe : ∀ j R R', (∀ k, k ≠ a → k ≠ t → R' k = R k) → Inv j R → Inv j R')
    (hp : ∀ j < N, ∀ (v : HS T Q A U) (S : Stacks T A), S.L = left → Inv j S.R →
      ∃ v' R' m, v'.user = v.user ∧ m ≤ c j ∧
        Exec body p (mk v S) m (mk v' {S with R := R'}) ∧
        R' a = S.R a ∧ R' t = S.R t ∧ Inv (j+1) R') :
    ∀ (l : List (Fin (A + 4))) (j : ℕ) (v : HS T Q A U) (S : Stacks T A), S.R a = l →
      j + l.length ≤ N → S.L = left → Inv j S.R → v.flag = l.head?.isSome →
      ∃ (v' : HS T Q A U) (R' : Regs T A) (m : ℕ), v'.user = v.user ∧
        m ≤ ∑ i ∈ Finset.range l.length, (c (j + i) + 3) + 1 ∧
        Exec body (.loop (·.flag) (.seq (.act (popPush a t)) (.seq p (.act (peekR a)))))
          (mk v S) m (mk v' { S with R := R' }) ∧
        R' a = [] ∧ R' t = l.reverse ++ S.R t ∧
        Inv (j+l.length) R'
  | [], j, v, S, hS, _, hL, hΨ, hfl =>
      ⟨v, S.R, 1, rfl, by simp, .loop_false (by simpa using hfl), hS, by simp,
        by simpa using hΨ⟩
  | x :: rest, j, v, S, hS, hN, hL, hΨ, hfl => by
      have hrun : (popPush a t : Act T Q A U).run (mk v S) = mk { v with sym := some x }
          { S with R := Function.update (Function.update S.R a rest) t (x :: S.R t) } := by
        simp [popPush, Action.run, hS, update_rt, Function.update_of_ne hat.symm]
      obtain ⟨v₁, R₁, m₁, hu₁, hm₁, he₁, ha₁, ht₁, hΨ₁⟩ := hp j (by simp at hN; omega)
        { v with sym := some x }
        { S with R := Function.update (Function.update S.R a rest) t (x :: S.R t) }
        hL (hframe j _ _ (fun k hka hkt => by simp [hka,hkt]) hΨ)
      have ha₁' : R₁ a = rest := by rw [ha₁]; simp [Function.update_of_ne hat]
      have he₂ := Exec.act (body := body) (peekR a) (mk v₁ { S with R := R₁ })
      rw [peekR_run] at he₂
      obtain ⟨v', R', m', hu', hm', he', ha', ht', hΨ'⟩  := scanInvariant_loop hat hframe hp rest (j + 1)
        { v₁ with flag := (R₁ a).head?.isSome } { S with R := R₁ } ha₁' (by simp at hN; omega) hL hΨ₁
        (by rw [ha₁'])
      refine ⟨v', R', 1 + (m₁ + 1) + m' + 1, by rw [hu', ← hu₁], ?_,
        Exec.loop_true (by simpa using hfl) (Exec.seq (hrun ▸ Exec.act (body := body) _ (mk v S))
          (Exec.seq he₁ he₂)) he', ha', ?_, ?_⟩
      · rw [List.length_cons, Finset.sum_range_succ']
        have : ∑ i ∈ Finset.range rest.length, (c (j + 1 + i) + 3) =
            ∑ i ∈ Finset.range rest.length, (c (j + (i + 1)) + 3) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Nat.add_assoc, Nat.add_comm 1 i]
        rw [← this]
        simp only [Nat.add_zero]
        omega
      · rw [ht']; dsimp only; rw [ht₁]; simp
      · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using hΨ' 

theorem scanInvariant_exec {a t : Fin T} (hat : a ≠ t) {p : Pr P T Q A U}
    {Inv : ℕ → Regs T A → Prop} {c : ℕ → ℕ} {N : ℕ} {left : Regs T A}
    (hframe : ∀ j R R', (∀ k, k ≠ a → k ≠ t → R' k = R k) → Inv j R → Inv j R')
    (hp : ∀ j < N, ∀ (v : HS T Q A U) (S : Stacks T A), S.L = left → Inv j S.R →
      ∃ v' R' m, v'.user = v.user ∧ m ≤ c j ∧
        Exec body p (mk v S) m (mk v' {S with R := R'}) ∧
        R' a = S.R a ∧ R' t = S.R t ∧ Inv (j+1) R')
    (j : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hN : j+(S.R a).length ≤ N) (hL : S.L = left) (hInv : Inv j S.R) :
    ∃ v' R' m, v'.user = v.user ∧
      m ≤ (∑ i ∈ Finset.range (S.R a).length, (c (j+i)+3))+2*(S.R a).length+2*(S.R t).length+4 ∧
      Exec body (scanP a t p) (mk v S) m (mk v' {S with R := R'}) ∧
      R' a = (S.R t).reverse++S.R a ∧ R' t = [] ∧ Inv (j+(S.R a).length) R' := by
  obtain ⟨v₁,R₁,m₁,hu₁,hm₁,he₁,ha₁,ht₁,hInv₁⟩ := scanInvariant_loop (body := body) hat hframe hp
    (S.R a) j {v with flag := (S.R a).head?.isSome} S rfl hN hL hInv rfl
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body t a hat.symm id v₁ {S with R := R₁}
  refine ⟨v₂,movedR R₁ t a id (R₁ t),_,hu₂.trans hu₁,?_,
    Exec.seq (peekR_run a v S ▸ Exec.act (body := body) (peekR a) (mk v S))
      (Exec.seq he₁ he₂),?_,?_,?_⟩
  · dsimp only
    rw [ht₁]
    simp
    omega
  · simp [movedR,ht₁,ha₁]
  · simp [movedR,ht₁,Function.update_of_ne hat.symm]
  · apply hframe _ R₁ _ ?_ hInv₁
    intro k hka hkt
    simp [movedR,hka,hkt]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
