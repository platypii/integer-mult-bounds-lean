module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorDimensions

/-! Compose generated multiplier readiness and all band/count/volume dimensions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryFactorHeaderSetup : Pr P 224 Q A U := .seq boundaryFactorMultiplierSetup boundaryFactorDimensions

def boundaryFactorHeaderR (q : ℕ) (R : Regs 224 A) : Regs 224 A :=
  UnarySetup.runR boundaryFactorDimensionOps (boundaryFactorCounterR q (2*q+8) R)

def boundaryFactorHeaderSetupCost (q band N : ℕ) : ℕ :=
  boundaryFactorMultiplierSetupCost q+boundaryFactorDimensionsCost band N (2*q+8)

theorem boundaryFactorHeaderSetup_exec (q band N : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q) (hband : (S.R 124).length = band) (hN : (S.R 116).length = N)
    (h184 : S.R 184 = []) (hclean : ∀ i : Fin 224, i.val < 26 → S.R i = [])
    (hblank : ∀ c : CR, S.R (boundaryFactorReg (.cm c)) = [])
    (hports : ∀ r ∈ boundaryFactorDimensionPorts, S.R r = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryFactorHeaderSetupCost q band N ∧
      Exec body boundaryFactorHeaderSetup (mk v S) n (mk v' {S with R := boundaryFactorHeaderR q S.R}) ∧
      RsbReady (boundaryFactorState {S with R := boundaryFactorHeaderR q S.R}) (2*q+8) q := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hready₁⟩ := boundaryFactorMultiplierSetup_exec (body := body) q v S
    hq h184 (hports 223 (by simp [boundaryFactorDimensionPorts])) hclean hblank
  let S₁ : Stacks 224 A := {S with R := boundaryFactorCounterR q (2*q+8) S.R}
  have hports₁ : ∀ r ∈ boundaryFactorDimensionPorts, S₁.R r = [] := by
    intro r hr
    have hne : r ≠ 160 ∧ r ≠ 161 ∧ r ≠ 162 := by
      simp only [boundaryFactorDimensionPorts,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,boundaryFactorCounterR,hne.1,hne.2.1,hne.2.2] using hports r hr
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryFactorDimensions_exec (body := body) band N (2*q+8) v₁ S₁
    (by simpa [S₁,boundaryFactorCounterR] using hband) (by simpa [S₁,boundaryFactorCounterR] using hN)
    (by simp [S₁,boundaryFactorCounterR])
    (by simpa [S₁,boundaryFactorCounterR] using hclean 0 (by decide))
    (by simpa [S₁,boundaryFactorCounterR] using hclean 1 (by decide)) hports₁
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,
    boundaryFactorDimensions_ready q (2*q+8) S₁ hready₁⟩

theorem boundaryFactorHeaderR_off (q : ℕ) (R : Regs 224 A) (i : Fin 224)
    (hports : i ∉ boundaryFactorDimensionPorts) (h160 : i ≠ 160) (h161 : i ≠ 161) (h162 : i ≠ 162) :
    boundaryFactorHeaderR q R i = R i := by
  rw [boundaryFactorHeaderR,boundaryFactorDimensions_off _ _ hports]
  simp [boundaryFactorCounterR,h160,h161,h162]

theorem boundaryFactorHeaderR_legacy (q : ℕ) (R : Regs 224 A) (i : Fin 154) :
    boundaryFactorHeaderR q R (boundaryFactorLegacyReg i) = R (boundaryFactorLegacyReg i) := by
  have hi := i.isLt
  have hports : boundaryFactorLegacyReg i ∉ boundaryFactorDimensionPorts := by
    simp only [boundaryFactorDimensionPorts,List.mem_cons,List.not_mem_nil,or_false]
    intro h
    rcases h with h | h | h | h | h | h | h | h | h <;>
      have hh := congrArg (fun j : Fin 224 => j.val) h <;>
      change i.val = _ at hh <;> omega
  rw [boundaryFactorHeaderR,boundaryFactorDimensions_off _ _ hports]
  have h160 : boundaryFactorLegacyReg i ≠ 160 := by intro h; have := congrArg Fin.val h; change i.val = 160 at this; omega
  have h161 : boundaryFactorLegacyReg i ≠ 161 := by intro h; have := congrArg Fin.val h; change i.val = 161 at this; omega
  have h162 : boundaryFactorLegacyReg i ≠ 162 := by intro h; have := congrArg Fin.val h; change i.val = 162 at this; omega
  simp [boundaryFactorCounterR,h160,h161,h162]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
