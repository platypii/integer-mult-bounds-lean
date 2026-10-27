module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorNewtonHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorSeed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! Generate the Newton count, encoded starting value and zero mask, preserving all other factor data. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryFactorConstants : Pr P 224 Q A U :=
  .seq boundaryFactorNewtonHeader (.seq boundaryFactorSeed (copyR 160 186 184 (fun _ => pairSym A false false)))

def boundaryFactorConstantsR (p q : ℕ) (R : Regs 224 A) : Regs 224 A :=
  Function.update (Function.update (Function.update R 191 (List.replicate (factorNewtonSteps p q) tick))
    218 (csyms A (2*q+8) (⟨(2 : ℤ)^(q-2),0⟩ : GaussianInt))) 186 (csyms A (2*q+8) 0)

def boundaryFactorConstantsCost (p q : ℕ) : ℕ :=
  boundaryFactorNewtonHeaderCost p q+(boundaryFactorSeedCost q+(4*(2*q+8)+4))

theorem boundaryFactorConstants_exec (p q : ℕ) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hp : (S.R 117).length = 2^15*p) (hq : (S.R 119).length = q) (hw : (S.R 160).length = 2*q+8)
    (hclean : ∀ i : Fin 224, i.val < 5 → S.R i = [])
    (hblank : ∀ i ∈ [(184 : Fin 224),223,221,191,218,186], S.R i = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ boundaryFactorConstantsCost p q ∧
      Exec body boundaryFactorConstants (mk v S) steps
        (mk v' {S with R := boundaryFactorConstantsR p q S.R}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := boundaryFactorNewtonHeader_exec (body := body) p q v S hp hq
    (hclean 0 (by decide)) (hclean 1 (by decide)) (hclean 2 (by decide))
    (hclean 3 (by decide)) (hclean 4 (by decide))
    (hblank 184 (by simp)) (hblank 223 (by simp)) (hblank 221 (by simp)) (hblank 191 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 191 (List.replicate (factorNewtonSteps p q) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := boundaryFactorSeed_exec (body := body) q v₁ S₁
    (by simpa [S₁] using hq) (by simpa [S₁] using hw) (by simpa [S₁] using hclean 0 (by decide))
    (by simpa [S₁] using hblank 184 (by simp)) (by simpa [S₁] using hblank 218 (by simp))
    (by simpa [S₁] using hblank 221 (by simp)) (by simpa [S₁] using hblank 223 (by simp))
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 218 (csyms A (2*q+8) (⟨(2 : ℤ)^(q-2),0⟩ : GaussianInt))}
  obtain ⟨v₃,hu₃,he₃⟩ := copyR_exec body 160 186 184 (by decide) (by decide) (by decide)
    (fun _ => pairSym A false false) v₂ S₂ (by simpa [S₂,S₁] using hblank 184 (by simp))
  have he₃' : Exec body (copyR 160 186 184 (fun _ => pairSym A false false)) (mk v₂ S₂) (4*(2*q+8)+4)
      (mk v₃ {S with R := boundaryFactorConstantsR p q S.R}) := by
    simpa [S₂,S₁,boundaryFactorConstantsR,ShortConv.csyms_zero,hw,hblank 186 (by simp)] using he₃
  exact ⟨v₃,m₁+(boundaryFactorSeedCost q+(4*(2*q+8)+4)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_right hm₁ _,Exec.seq he₁ (Exec.seq he₂ he₃')⟩

theorem boundaryFactorConstantsR_ready (p q w : ℕ) (S : Stacks 224 A)
    (hready : RsbReady (boundaryFactorState S) w q) :
    RsbReady (boundaryFactorState {S with R := boundaryFactorConstantsR p q S.R}) w q := by
  have hcm (c : CR) : boundaryFactorConstantsR p q S.R (boundaryFactorReg (.cm c)) =
      S.R (boundaryFactorReg (.cm c)) := by cases c <;> rfl
  constructor
  · change (boundaryFactorConstantsR p q S.R (boundaryFactorReg (.cm .wn))).length = w
    rw [hcm]; exact hready.wn
  · change (boundaryFactorConstantsR p q S.R (boundaryFactorReg (.cm .pn))).length = q
    rw [hcm]; exact hready.pn
  · change (boundaryFactorConstantsR p q S.R (boundaryFactorReg (.cm .nn))).length = _
    rw [hcm]; exact hready.nn
  · intro c hxs hys hout hwn hpn hnn
    change boundaryFactorConstantsR p q S.R (boundaryFactorReg (.cm c)) = []
    rw [hcm]
    exact hready.empty c hxs hys hout hwn hpn hnn

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
