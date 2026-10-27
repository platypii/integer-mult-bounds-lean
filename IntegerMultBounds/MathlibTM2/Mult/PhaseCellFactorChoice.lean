module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryIfLeSum

/-! Runtime boundary-rank and band tests select lookup or zero padding with all test scratch released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def FactorRankValid (N W n m : ℕ) : Prop := n < N ∧ m < N ∧ n ≤ m+W ∧ m ≤ n+W
instance (N W n m : ℕ) : Decidable (FactorRankValid N W n m) := by unfold FactorRankValid; infer_instance

def factorChoice (yes no : Pr P 154 Q A U) : Pr P 154 Q A U :=
  unaryIfLt 107 116 1 2 (unaryIfLt 108 116 1 2
    (unaryIfLeSum 107 108 94 3 1 2 (unaryIfLeSum 108 107 94 3 1 2 yes no) no) no) no

def factorChoiceCost (n m W N : ℕ) : ℕ :=
  unaryIfLtCost n N+(unaryIfLtCost m N+(unaryIfLeSumCost n m W+unaryIfLeSumCost m n W))

theorem factorChoice_exec (yes no : Pr P 154 Q A U) (n m W N budget : ℕ) (S S' : Stacks 154 A)
    (hn : (S.R 107).length = n) (hm : (S.R 108).length = m) (hW : (S.R 94).length = W) (hN : (S.R 116).length = N)
    (hfresh : ∀ k ∈ [(1 : Fin 154),2,3], S.R k = [])
    (hbranch : ∀ vi : HS 154 Q A U, ∃ v' steps, v'.user = vi.user ∧ steps ≤ budget ∧
      Exec body (if FactorRankValid N W n m then yes else no) (mk vi S) steps (mk v' S'))
    (v : HS 154 Q A U) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorChoiceCost n m W N+budget ∧
      Exec body (factorChoice yes no) (mk v S) steps (mk v' S') := by
  let p₄ := unaryIfLeSum 108 107 94 3 1 2 yes no
  let p₃ := unaryIfLeSum 107 108 94 3 1 2 p₄ no
  let p₂ := unaryIfLt 108 116 1 2 p₃ no
  let c₄ := unaryIfLeSumCost m n W
  let c₃ := unaryIfLeSumCost n m W
  let c₂ := unaryIfLtCost m N
  have h4 : n < N → m < N → n ≤ m+W → ∀ vi : HS 154 Q A U,
      ∃ v' steps, v'.user = vi.user ∧ steps ≤ c₄+budget ∧ Exec body p₄ (mk vi S) steps (mk v' S') := by
    intro hnN hmN hnW vi
    apply unaryIfLeSum_exec (body := body) (a := 108) (b := 107) (band := 94) (endpoint := 3) (work := 1) (tmp := 2)
      (by decide) yes no m n W budget S S' hm hn hW (by
        intro k hk
        exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)) ?_ vi
    intro vj
    simpa only [FactorRankValid,hnN,hmN,hnW,true_and] using hbranch vj
  have h3 : n < N → m < N → ∀ vi : HS 154 Q A U,
      ∃ v' steps, v'.user = vi.user ∧ steps ≤ c₃+(c₄+budget) ∧ Exec body p₃ (mk vi S) steps (mk v' S') := by
    intro hnN hmN vi
    apply unaryIfLeSum_exec (body := body) (a := 107) (b := 108) (band := 94) (endpoint := 3) (work := 1) (tmp := 2)
      (by decide) p₄ no n m W (c₄+budget) S S' hn hm hW (by
        intro k hk
        exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)) ?_ vi
    intro vj
    by_cases hnW : n ≤ m+W
    · simpa only [hnW,ite_true] using h4 hnN hmN hnW vj
    · obtain ⟨v',steps,hu,hs,he⟩ := hbranch vj
      exact ⟨v',steps,hu,by omega,by simpa [FactorRankValid,hnW] using he⟩
  have h2 : n < N → ∀ vi : HS 154 Q A U,
      ∃ v' steps, v'.user = vi.user ∧ steps ≤ c₂+(c₃+(c₄+budget)) ∧ Exec body p₂ (mk vi S) steps (mk v' S') := by
    intro hnN vi
    apply unaryIfLt_exec (body := body) (a := 108) (b := 116) (work := 1) (tmp := 2) (by decide)
      p₃ no m N (c₃+(c₄+budget)) S S' hm hN (hfresh 1 (by simp)) (hfresh 2 (by simp)) ?_ vi
    intro vj
    by_cases hmN : m < N
    · simpa only [hmN,ite_true] using h3 hnN hmN vj
    · obtain ⟨v',steps,hu,hs,he⟩ := hbranch vj
      exact ⟨v',steps,hu,by omega,by simpa [FactorRankValid,hmN] using he⟩
  obtain ⟨v',steps,hu,hs,he⟩ := unaryIfLt_exec (body := body) (a := 107) (b := 116) (work := 1) (tmp := 2)
    (by decide) p₂ no n N (c₂+(c₃+(c₄+budget))) S S' hn hN (hfresh 1 (by simp)) (hfresh 2 (by simp)) (by
      intro vj
      by_cases hnN : n < N
      · simpa only [hnN,ite_true] using h2 hnN vj
      · obtain ⟨v',steps,hu,hs,he⟩ := hbranch vj
        exact ⟨v',steps,hu,by omega,by simpa [FactorRankValid,hnN] using he⟩) v
  exact ⟨v',steps,hu,by simpa [factorChoiceCost,c₂,c₃,c₄,Nat.add_assoc] using hs,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
