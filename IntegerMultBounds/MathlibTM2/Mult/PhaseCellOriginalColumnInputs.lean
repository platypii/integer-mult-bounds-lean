module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNegativeUnitField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace

/-! Generate both column sources from reusable coupling headers and a retained coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def originalColumnInputs : Pr P₀ 144 Q A U :=
  .seq (zeroWords 97 94 110 134 135 137) negativeUnitBasis

def originalColumnInputsCost (s w q : ℕ) : ℕ := 20*s*w+26*s+2*q+50

theorem originalColumnInputs_exec {P q w s t u band a b : ℕ} [NeZero s] (hq : q ≤ w)
    (j : ZMod s) (tail : List (Fin (A+4))) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hready : CouplingReady P q w s t u band a b tail (embStk groupReg S))
    (hcoordinate : (S.R 136).length = j.val)
    (h131 : S.R 131 = []) (h134 : S.R 134 = []) (h135 : S.R 135 = []) (h137 : S.R 137 = []) :
    let rhs := cstream A w (chirpLine s (fun _ => 0))++tail
    let basis := cstream A w (chirpLine s (negativeUnitField q j))++S.R 132
    let S' : Stacks 144 A := {S with R := Function.update (Function.update S.R 110 rhs) 132 basis}
    ∃ v' m, v'.user = v.user ∧ m ≤ originalColumnInputsCost s w q ∧
      Exec (embTab groupReg body) originalColumnInputs (mk v S) m (mk v' S') ∧
      CouplingReady P q w s t u band a b rhs (embStk groupReg S') := by
  dsimp only
  have hs : (S.R 97).length = s := hready.axis
  have hw : (S.R 94).length = w := hready.width
  have hqS : (S.R 112).length = q := hready.fraction
  have hsource : S.R 110 = tail := hready.source
  have hzero : List.replicate s (0 : GaussianInt) = chirpLine s (fun _ => 0) := by simp [chirpLine]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := zeroWords_exec (body := embTab groupReg body)
    (rows := 97) (width := 94) (dst := 110) (count := 134) (saved := 135) (tmp := 137)
    (by decide) s w v S hs hw h134 h135 h137
  let rhs := cstream A w (chirpLine s (fun _ => 0))++tail
  let basis := cstream A w (chirpLine s (negativeUnitField q j))++S.R 132
  let S₁ : Stacks 144 A := {S with R := Function.update S.R 110 rhs}
  have he₁' : Exec (embTab groupReg body) (zeroWords 97 94 110 134 135 137) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hzero,hsource] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := negativeUnitBasis_exec (body := embTab groupReg body) s j.val w q j.val_lt hq
    v₁ S₁ (by simpa [S₁] using hs) (by simpa [S₁] using hcoordinate)
    (by simpa [S₁] using hw) (by simpa [S₁] using hqS)
    (by simpa [S₁] using h131) (by simpa [S₁] using h134)
    (by simpa [S₁] using h135) (by simpa [S₁] using h137)
  let S₂ : Stacks 144 A := {S₁ with R := Function.update S₁.R 132 basis}
  have he₂' : Exec (embTab groupReg body) negativeUnitBasis (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa [S₂,S₁,basis,← negativeUnitField_words q j] using he₂
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁' he₂',?_⟩
  · dsimp [originalColumnInputsCost]
    nlinarith only [hm₁,hm₂]
  · apply hready.of_source_frame (S' := embStk groupReg S₂) (raw' := rhs) (by simp [S₂,S₁,embStk,groupReg]) rfl
    intro k _ _ _ h110
    have h110' : groupReg k ≠ (110 : Fin 144) := by simpa [groupReg,Fin.ext_iff] using h110
    have h132 : groupReg k ≠ (132 : Fin 144) := by have := k.isLt; simp [groupReg,Fin.ext_iff]; omega
    simp [S₂,S₁,embStk,Function.comp_def,h110',h132]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
