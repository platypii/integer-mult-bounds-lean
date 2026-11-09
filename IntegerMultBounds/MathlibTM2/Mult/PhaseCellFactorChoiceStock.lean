module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorChoice
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnaryIfLeSumStock

/-! Factor-entry selection separates comparison setup from the chosen branch reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

theorem factorChoice_exec_within (yes no : Pr P 154 Q A U) (n m W N budget reserve depth : ℕ) (S S' : Stacks 154 A)
    (hn : (S.R 107).length = n) (hm : (S.R 108).length = m) (hW : (S.R 94).length = W) (hN : (S.R 116).length = N)
    (hfresh : ∀ k ∈ [(1 : Fin 154),2,3], S.R k = [])
    (hbranch : ∀ vi : HS 154 Q A U, ∃ v' steps, v'.user = vi.user ∧ steps ≤ budget ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi S)+depth+reserve)
        depth (if FactorRankValid N W n m then yes else no) (mk vi S) steps (mk v' S'))
    (v : HS 154 Q A U) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorChoiceCost n m W N+budget ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(2*factorChoiceCost n m W N+reserve))
        depth (factorChoice yes no) (mk v S) steps (mk v' S') := by
  let p₄ := unaryIfLeSum 108 107 94 3 1 2 yes no
  let p₃ := unaryIfLeSum 107 108 94 3 1 2 p₄ no
  let p₂ := unaryIfLt 108 116 1 2 p₃ no
  let c₄ := unaryIfLeSumCost m n W
  let c₃ := unaryIfLeSumCost n m W
  let c₂ := unaryIfLtCost m N
  have h4 : n < N → m < N → n ≤ m+W → ∀ vi : HS 154 Q A U,
      ∃ v' steps, v'.user = vi.user ∧ steps ≤ c₄+budget ∧ ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi S)+depth+(2*c₄+reserve)) depth p₄ (mk vi S) steps (mk v' S') := by
    intro hnN hmN hnW vi
    apply unaryIfLeSum_exec_within (body := body) (a := 108) (b := 107) (band := 94) (endpoint := 3) (work := 1) (tmp := 2)
      (by decide) yes no m n W budget reserve depth S S' hm hn hW (by
        intro k hk
        exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)) ?_ vi
    intro vj
    simpa only [FactorRankValid,hnN,hmN,hnW,true_and] using hbranch vj
  have h3 : n < N → m < N → ∀ vi : HS 154 Q A U,
      ∃ v' steps, v'.user = vi.user ∧ steps ≤ c₃+(c₄+budget) ∧ ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi S)+depth+(2*c₃+(2*c₄+reserve))) depth p₃ (mk vi S) steps (mk v' S') := by
    intro hnN hmN vi
    apply unaryIfLeSum_exec_within (body := body) (a := 107) (b := 108) (band := 94) (endpoint := 3) (work := 1) (tmp := 2)
      (by decide) p₄ no n m W (c₄+budget) (2*c₄+reserve) depth S S' hn hm hW (by
        intro k hk
        exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)) ?_ vi
    intro vj
    by_cases hnW : n ≤ m+W
    · simpa only [hnW,ite_true] using h4 hnN hmN hnW vj
    · obtain ⟨v',steps,hu,hs,he⟩ := hbranch vj
      exact ⟨v',steps,hu,by omega,by
        have h := he.mono (J := fun d z => mnSize z+d ≤ mnSize (mk vj S)+depth+(2*c₄+reserve))
          (by intro d z hz; omega)
        simpa [FactorRankValid,hnW] using h⟩
  have h2 : n < N → ∀ vi : HS 154 Q A U,
      ∃ v' steps, v'.user = vi.user ∧ steps ≤ c₂+(c₃+(c₄+budget)) ∧ ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi S)+depth+(2*c₂+(2*c₃+(2*c₄+reserve)))) depth p₂ (mk vi S) steps (mk v' S') := by
    intro hnN vi
    apply unaryIfLt_exec_within (body := body) (a := 108) (b := 116) (work := 1) (tmp := 2) (by decide)
      p₃ no m N (c₃+(c₄+budget)) (2*c₃+(2*c₄+reserve)) depth S S' hm hN (hfresh 1 (by simp)) (hfresh 2 (by simp)) ?_ vi
    intro vj
    by_cases hmN : m < N
    · simpa only [hmN,ite_true] using h3 hnN hmN vj
    · obtain ⟨v',steps,hu,hs,he⟩ := hbranch vj
      exact ⟨v',steps,hu,by omega,by
        have h := he.mono (J := fun d z => mnSize z+d ≤ mnSize (mk vj S)+depth+(2*c₃+(2*c₄+reserve)))
          (by intro d z hz; omega)
        simpa [FactorRankValid,hmN] using h⟩
  obtain ⟨v',steps,hu,hs,he⟩ := unaryIfLt_exec_within (body := body) (a := 107) (b := 116) (work := 1) (tmp := 2)
    (by decide) p₂ no n N (c₂+(c₃+(c₄+budget))) (2*c₂+(2*c₃+(2*c₄+reserve))) depth S S' hn hN (hfresh 1 (by simp)) (hfresh 2 (by simp)) (by
      intro vj
      by_cases hnN : n < N
      · simpa only [hnN,ite_true] using h2 hnN vj
      · obtain ⟨v',steps,hu,hs,he⟩ := hbranch vj
        exact ⟨v',steps,hu,by omega,by
          have h := he.mono (J := fun d z => mnSize z+d ≤ mnSize (mk vj S)+depth+(2*c₂+(2*c₃+(2*c₄+reserve))))
            (by intro d z hz; omega)
          simpa [FactorRankValid,hnN] using h⟩) v
  exact ⟨v',steps,hu,by simpa [factorChoiceCost,c₂,c₃,c₄,Nat.add_assoc] using hs,he.mono (by
    intro d z hz
    dsimp only [factorChoiceCost,c₂,c₃,c₄]
    omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
