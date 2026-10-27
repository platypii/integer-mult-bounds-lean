module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorCounters

/-! Generate the complete factor multiplier readiness from retained precision and release its private width header. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem boundaryFactorCounterR_ready (q w : ℕ) (S : Stacks 224 A)
    (hblank : ∀ c : CR, S.R (boundaryFactorReg (.cm c)) = []) :
    RsbReady (boundaryFactorState {S with R := boundaryFactorCounterR q w S.R}) w q := by
  constructor
  · simp [boundaryFactorState,boundaryFactorCounterR,boundaryFactorReg]
  · simp [boundaryFactorState,boundaryFactorCounterR,boundaryFactorReg]
  · simp [boundaryFactorState,boundaryFactorCounterR,boundaryFactorReg]
  · intro c hxs hys hout hwn hpn hnn
    change boundaryFactorCounterR q w S.R (boundaryFactorReg (.cm c)) = []
    have hoff : boundaryFactorCounterR q w S.R (boundaryFactorReg (.cm c)) = S.R (boundaryFactorReg (.cm c)) := by
      cases c <;> simp_all [boundaryFactorCounterR,boundaryFactorReg]
    exact hoff.trans (hblank c)

def boundaryFactorMultiplierSetup : Pr P 224 Q A U :=
  .seq (generateWordWidth 119 223 184) (.seq boundaryFactorCountersFromWidth (uclear 223))

def boundaryFactorMultiplierSetupCost (q : ℕ) : ℕ :=
  (8*q+9)+(ScalarPlacement.prepareCost q (2*q+8)+(2*(2*q+8)+2))

theorem boundaryFactorMultiplierSetup_exec (q : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hq : (S.R 119).length = q) (h184 : S.R 184 = []) (h223 : S.R 223 = [])
    (hclean : ∀ i : Fin 224, i.val < 26 → S.R i = [])
    (hblank : ∀ c : CR, S.R (boundaryFactorReg (.cm c)) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ boundaryFactorMultiplierSetupCost q ∧
      Exec body boundaryFactorMultiplierSetup (mk v S) m
        (mk v' {S with R := boundaryFactorCounterR q (2*q+8) S.R}) ∧
      RsbReady (boundaryFactorState {S with R := boundaryFactorCounterR q (2*q+8) S.R}) (2*q+8) q := by
  let w := 2*q+8
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (show [(119 : Fin 224),223,184].Nodup by decide) q v S hq h223 h184
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 223 (List.replicate w tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := boundaryFactorCountersFromWidth_exec (body := body) q w
    (by dsimp [w]; omega) (by dsimp [w]; omega) v₁ S₁
    (by simpa [S₁] using hq) (by simp [S₁])
    (by
      intro i hi
      have hi223 : i ≠ 223 := by omega
      simpa [S₁,hi223] using hclean i hi)
    (by
      exact ⟨by simpa [S₁,boundaryFactorReg] using hblank .wn,
        by simpa [S₁,boundaryFactorReg] using hblank .pn,
        by simpa [S₁,boundaryFactorReg] using hblank .nn⟩)
  let S₂ : Stacks 224 A := {S₁ with R := boundaryFactorCounterR q w S₁.R}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 223 v₂ S₂
  have hlen : (S₂.R 223).length = w := by simp [S₂,S₁,boundaryFactorCounterR]
  refine ⟨v₃,(8*q+9)+(m₂+(2*w+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hlen]) ?_,boundaryFactorCounterR_ready q w S hblank⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi223 : i = 223 <;> by_cases hi160 : i = 160 <;>
    by_cases hi161 : i = 161 <;> by_cases hi162 : i = 162 <;>
    simp [S₂,S₁,boundaryFactorCounterR,w,hi223,hi160,hi161,hi162,h223]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
