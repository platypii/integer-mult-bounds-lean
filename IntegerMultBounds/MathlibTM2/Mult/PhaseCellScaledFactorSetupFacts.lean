module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSetupFacts

/-! Concrete dimensions and clean factor scratch follow from the generated setup's exact frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {A : ℕ}

theorem scaledFactorSetupR_off (factor p q : ℕ) (R : Regs 224 A) (i : Fin 224)
    (hports : i ∉ boundaryFactorDimensionPorts) (h160 : i ≠ 160) (h161 : i ≠ 161) (h162 : i ≠ 162)
    (h191 : i ≠ 191) (h218 : i ≠ 218) (h186 : i ≠ 186) :
    scaledFactorSetupR factor p q R i = R i := by
  simp only [scaledFactorSetupR,boundaryFactorConstantsR,Function.update_of_ne h191,
    Function.update_of_ne h218,Function.update_of_ne h186]
  exact scaledFactorHeaderR_off factor q R i hports h160 h161 h162

theorem scaledFactorSetupR_empty (factor p q : ℕ) (R : Regs 224 A)
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → R i = []) :
    ∀ r ∈ boundaryFactorScratch, scaledFactorSetupR factor p q R (boundaryFactorReg r) = [] := by
  have hroles : ∀ r ∈ boundaryFactorScratch,
      154 ≤ (boundaryFactorReg r).val ∧ boundaryFactorReg r ∉ boundaryFactorDimensionPorts ∧
      boundaryFactorReg r ≠ 160 ∧ boundaryFactorReg r ≠ 161 ∧ boundaryFactorReg r ≠ 162 ∧
      boundaryFactorReg r ≠ 191 ∧ boundaryFactorReg r ≠ 218 ∧ boundaryFactorReg r ≠ 186 := by decide
  intro r hr
  obtain ⟨hge,hports,h160,h161,h162,h191,h218,h186⟩ := hroles r hr
  rw [scaledFactorSetupR_off factor p q R _ hports h160 h161 h162 h191 h218 h186]
  exact hnew _ hge

theorem scaledFactorSetupR_dimensions (factor p q band N : ℕ) (R : Regs 224 A)
    (hband : (R 124).length = band) (hN : (R 116).length = N)
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → R i = []) :
    let R' := scaledFactorSetupR factor p q R
    (R' 185).length = factor*band ∧ (R' 187).length = factor*band+1 ∧
    (R' 190).length = 2*(factor*band+1) ∧ (R' 192).length = N ∧
    (R' 189).length = (factor*band)*(2*q+8) ∧ (R' 188).length = 2*(factor*band+1)*(2*q+8) ∧
    (R' 193).length = (2*(factor*band+1)+1)*(2*q+8) ∧
    (R' 194).length = (factor*band+1+1)*(2*(factor*band+1)+1)*(2*q+8) ∧ R' 223 = [] := by
  let C := boundaryFactorCounterR q (2*q+8) R
  have hports : ∀ i ∈ boundaryFactorDimensionPorts, C i = [] := by
    intro i hi
    have hge : 154 ≤ i.val ∧ i ≠ 160 ∧ i ≠ 161 ∧ i ≠ 162 := by
      simp only [boundaryFactorDimensionPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [C,boundaryFactorCounterR,hge.2.1,hge.2.2.1,hge.2.2.2] using hnew i hge.1
  have hd := scaledFactorDimensions_lengths factor band N (2*q+8) C
    (by simpa [C,boundaryFactorCounterR] using hband) (by simpa [C,boundaryFactorCounterR] using hN)
    (by simp [C,boundaryFactorCounterR]) hports
  simpa [scaledFactorSetupR,boundaryFactorConstantsR,scaledFactorHeaderR,C] using hd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
