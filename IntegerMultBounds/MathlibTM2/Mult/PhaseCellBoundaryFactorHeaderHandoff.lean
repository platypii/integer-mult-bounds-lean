module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorHeaderSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageReady

/-! A structural handoff from any constructed legacy table state to physical factor headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 224 Q A U}

theorem boundaryFactorHeaderHandoff_exec (P N q l s t u band V w card : ℕ)
    (input : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A) (E₁ : Stacks 154 A)
    (hready : LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (hkeepE : ∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 → i ≠ 140 →
      E₁.R i = S.R (boundaryFactorLegacyReg i))
    (hcard : (E₁.R 116).length = card)
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    let S₁ := embOvr boundaryFactorLegacyReg E₁.get S
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryFactorHeaderSetupCost q band card ∧
      Exec body boundaryFactorHeaderSetup (mk v S₁) n
        (mk v' {S₁ with R := boundaryFactorHeaderR q S₁.R}) ∧
      RsbReady (boundaryFactorState {S₁ with R := boundaryFactorHeaderR q S₁.R}) (2*q+8) q := by
  let S₁ := embOvr boundaryFactorLegacyReg E₁.get S
  have hproj : embStk boundaryFactorLegacyReg S₁ = E₁ := embStk_ovr boundaryFactorLegacyReg_injective E₁ S
  have hkeep (i : Fin 154) (h109 : i ≠ 109) (h115 : i ≠ 115) (h116 : i ≠ 116) (h132 : i ≠ 132) (h140 : i ≠ 140) :
      S₁.R (boundaryFactorLegacyReg i) = S.R (boundaryFactorLegacyReg i) := by
    have hh := congrArg (fun X : Stacks 154 A => X.R i) hproj
    change S₁.R (boundaryFactorLegacyReg i) = E₁.R i at hh
    exact hh.trans (hkeepE i h109 h115 h116 h132 h140)
  have hq : (S₁.R 119).length = q := by
    rw [show S₁.R 119 = S.R 119 from hkeep 119 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (119,112) (by simp [groupHeaderCopies])
  have hb : (S₁.R 124).length = band := by
    rw [show S₁.R 124 = S.R 124 from hkeep 124 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (124,100) (by simp [groupHeaderCopies])
  have hN : (S₁.R 116).length = card := by
    have hh := congrArg (fun X : Stacks 154 A => (X.R 116).length) hproj
    change (S₁.R 116).length = (E₁.R 116).length at hh
    exact hh.trans hcard
  have hfresh (i : Fin 224) (hi : 154 ≤ i.val) : S₁.R i = [] := by
    have hoff : ∀ j : Fin 154, boundaryFactorLegacyReg j ≠ i := by
      intro j h
      have hh := congrArg Fin.val h
      change j.val = i.val at hh
      have := j.isLt
      omega
    exact ((embOvr_off E₁.get S hoff).2).trans (hnew i hi)
  have hclean (i : Fin 224) (hi : i.val < 26) : S₁.R i = [] := by
    let j : Fin 144 := ⟨i.val,by omega⟩
    have hj : j.val < 26 := hi
    have hh := hready.blank j (by omega) (by omega) (by omega)
    have he : boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg j))) = i := by
      have h109 : componentReg j ≠ 109 := by intro h; have := congrArg Fin.val h; change i.val = 109 at this; omega
      have h115 : componentReg j ≠ 115 := by intro h; have := congrArg Fin.val h; change i.val = 115 at this; omega
      have h116 : componentReg j ≠ 116 := by intro h; have := congrArg Fin.val h; change i.val = 116 at this; omega
      apply Fin.ext
      change (boundaryArithmeticReg (componentReg j)).val = i.val
      simp only [boundaryArithmeticReg,h109,h115,h116,ite_false]
      rfl
    change S.R (boundaryFactorLegacyReg (tableReg (boundaryArithmeticReg (componentReg j)))) = [] at hh
    rw [he] at hh
    let k : Fin 154 := ⟨i.val,by omega⟩
    have hk : boundaryFactorLegacyReg k = i := Fin.ext rfl
    rw [←hk,hkeep k (by omega) (by omega) (by omega) (by omega) (by omega),hk]
    exact hh
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃,hrdy₃⟩ := boundaryFactorHeaderSetup_exec
    (body := body)
    q band card v S₁ hq hb hN (hfresh 184 (by decide)) hclean
    (by intro c; apply hfresh; cases c <;> decide)
    (by intro i hi; apply hfresh; simp only [boundaryFactorDimensionPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  exact ⟨v₃,n₃,hu₃,hn₃,he₃,hrdy₃⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
