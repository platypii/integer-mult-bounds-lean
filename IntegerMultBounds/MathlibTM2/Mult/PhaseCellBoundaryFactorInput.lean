module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorHeaderHandoff

/-! The constructed legacy table frame supplies all physical factorization input controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

structure BoundaryFactorInput {A : ℕ} (P q band card : ℕ) (S : Stacks 224 A) : Prop where
  masterP : (S.R 117).length = P
  masterQ : (S.R 119).length = q
  band : (S.R 124).length = band
  card : (S.R 116).length = card
  left : ∀ i, S.L i = []
  clean : ∀ i : Fin 224, i.val < 64 → S.R i = []
  fresh : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []

variable {A : ℕ}

theorem boundaryFactorLegacy_input (P N q l s t u band V w card : ℕ)
    (input : List (Fin (A+4))) (S : Stacks 224 A) (E₁ : Stacks 154 A)
    (hready : LengthKeyReady P N q l s t u band V w input
      (embStk componentReg (embStk boundaryArithmeticReg (embStk tableReg (embStk boundaryFactorLegacyReg S)))))
    (hkeepE : ∀ i : Fin 154, i ≠ 109 → i ≠ 115 → i ≠ 116 → i ≠ 132 → i ≠ 140 →
      E₁.R i = S.R (boundaryFactorLegacyReg i))
    (hcard : (E₁.R 116).length = card) (hleftE : E₁.L = (embStk boundaryFactorLegacyReg S).L)
    (hleft : ∀ i : Fin 224, S.L i = [])
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    BoundaryFactorInput P q band card (embOvr boundaryFactorLegacyReg E₁.get S) := by
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
  have hclean (i : Fin 224) (hi : i.val < 64) : S₁.R i = [] := by
    let j : Fin 144 := ⟨i.val,by omega⟩
    have hj : j.val < 64 := hi
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
  have hP : (S₁.R 117).length = P := by
    rw [show S₁.R 117 = S.R 117 from hkeep 117 (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [embStk,componentReg,boundaryArithmeticReg,tableReg,boundaryFactorLegacyReg,groupHeaderValue] using
      hready.masters (117,114) (by simp [groupHeaderCopies])
  have hL : S₁.L = S.L := by
    change embExt boundaryFactorLegacyReg E₁.L S.L = S.L
    rw [hleftE]
    exact embExt_comp (e := boundaryFactorLegacyReg) S.L
  exact ⟨hP,hq,hb,hN,fun i => by rw [hL]; exact hleft i,hclean,hfresh⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
