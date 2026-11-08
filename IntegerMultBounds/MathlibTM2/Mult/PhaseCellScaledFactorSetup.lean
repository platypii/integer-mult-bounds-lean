module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorHeaderSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorConstants

/-! Generate all physical factor readiness, dimensions, Newton controls and encoded constants. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def scaledFactorSetup (factor : ℕ) : Pr P 224 Q A U := .seq (scaledFactorHeaderSetup factor) boundaryFactorConstants

def scaledFactorSetupR (factor p q : ℕ) (R : Regs 224 A) : Regs 224 A :=
  boundaryFactorConstantsR p q (scaledFactorHeaderR factor q R)

def scaledFactorSetupCost (factor p q band N : ℕ) : ℕ :=
  scaledFactorHeaderSetupCost factor q band N+boundaryFactorConstantsCost p q

theorem scaledFactorSetup_exec (factor p q band N : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hp : (S.R 117).length = 2^15*p) (hq : (S.R 119).length = q)
    (hband : (S.R 124).length = band) (hN : (S.R 116).length = N)
    (hclean : ∀ i : Fin 224, i.val < 26 → S.R i = [])
    (hnew : ∀ i : Fin 224, 154 ≤ i.val → S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ scaledFactorSetupCost factor p q band N ∧
      Exec body (scaledFactorSetup factor) (mk v S) n (mk v' {S with R := scaledFactorSetupR factor p q S.R}) ∧
      RsbReady (boundaryFactorState {S with R := scaledFactorSetupR factor p q S.R}) (2*q+8) q := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hrdy₁⟩ := scaledFactorHeaderSetup_exec (body := body) factor q band N v S hq hband hN
    (hnew 184 (by decide)) hclean (by intro c; apply hnew; cases c <;> decide)
    (by
      intro i hi
      apply hnew
      simp only [boundaryFactorDimensionPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  let S₁ : Stacks 224 A := {S with R := scaledFactorHeaderR factor q S.R}
  have hsmall (i : Fin 224) (hi : i.val < 5) : S₁.R i = [] := by
    let j : Fin 154 := ⟨i.val,by omega⟩
    have hj : boundaryFactorLegacyReg j = i := Fin.ext rfl
    have hh := scaledFactorHeaderR_legacy factor q S.R j
    rw [hj] at hh
    exact hh.trans (hclean i (by omega))
  have hblank : ∀ i ∈ [(184 : Fin 224),223,221,191,218,186], S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (scaledFactorHeaderR_off factor q S.R 184 (by decide) (by decide) (by decide) (by decide)).trans (hnew 184 (by decide))
    · rfl
    · exact (scaledFactorHeaderR_off factor q S.R 221 (by decide) (by decide) (by decide) (by decide)).trans (hnew 221 (by decide))
    · exact (scaledFactorHeaderR_off factor q S.R 191 (by decide) (by decide) (by decide) (by decide)).trans (hnew 191 (by decide))
    · exact (scaledFactorHeaderR_off factor q S.R 218 (by decide) (by decide) (by decide) (by decide)).trans (hnew 218 (by decide))
    · exact (scaledFactorHeaderR_off factor q S.R 186 (by decide) (by decide) (by decide) (by decide)).trans (hnew 186 (by decide))
  have hp₁ : (S₁.R 117).length = 2^15*p := by
    have hh : S₁.R 117 = S.R 117 := scaledFactorHeaderR_legacy factor q S.R 117
    rw [hh]; exact hp
  have hq₁ : (S₁.R 119).length = q := by
    have hh : S₁.R 119 = S.R 119 := scaledFactorHeaderR_legacy factor q S.R 119
    rw [hh]; exact hq
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryFactorConstants_exec (body := body) p q v₁ S₁ hp₁ hq₁ hrdy₁.wn hsmall hblank
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,
    boundaryFactorConstantsR_ready p q (2*q+8) S₁ hrdy₁⟩

theorem scaledFactorSetupR_legacy (factor p q : ℕ) (R : Regs 224 A) (i : Fin 154) :
    scaledFactorSetupR factor p q R (boundaryFactorLegacyReg i) = R (boundaryFactorLegacyReg i) := by
  have hi := i.isLt
  have h191 : boundaryFactorLegacyReg i ≠ 191 := by intro h; have := congrArg Fin.val h; change i.val = 191 at this; omega
  have h218 : boundaryFactorLegacyReg i ≠ 218 := by intro h; have := congrArg Fin.val h; change i.val = 218 at this; omega
  have h186 : boundaryFactorLegacyReg i ≠ 186 := by intro h; have := congrArg Fin.val h; change i.val = 186 at this; omega
  simp only [scaledFactorSetupR,boundaryFactorConstantsR,Function.update_of_ne h191,
    Function.update_of_ne h218,Function.update_of_ne h186,scaledFactorHeaderR_legacy]

theorem scaledFactorSetupR_constants (factor p q : ℕ) (R : Regs 224 A) :
    let R' := scaledFactorSetupR factor p q R
    (R' (boundaryFactorReg .kn)).length = factorNewtonSteps p q ∧
      R' (boundaryFactorReg .bx) = csyms A (2*q+8) (⟨(2 : ℤ)^(q-2),0⟩ : GaussianInt) ∧
      R' (boundaryFactorReg .msk) = csyms A (2*q+8) 0 := by
  simp [scaledFactorSetupR,boundaryFactorConstantsR,boundaryFactorReg]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
