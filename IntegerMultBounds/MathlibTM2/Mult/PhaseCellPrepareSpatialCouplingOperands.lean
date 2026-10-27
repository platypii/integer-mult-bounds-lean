module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyCountedLine
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareSpatialCouplingCoefficients

/-! Generate spatial coefficients and copy their aligned window from a positioned source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareSpatialCouplingOperands : Pr P₀ 117 Q A U :=
  .seq prepareSpatialCouplingCoefficients (copyCountedLine 102 94 92 110 109 104 105)

def prepareSpatialCouplingOperandsCost (P q w s t u band i : ℕ) : ℕ :=
  prepareSpatialCouplingCoefficientsCost P q w s t u band i + copyCountedLineCost (2*band+1) w

theorem prepareSpatialCouplingOperands_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) 
    (hst : s < t) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (hsrc : S.R 92 = cstream A w ((cyclicPaddedLine (fun j : ZMod s =>
      if j ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
      then C j else 0) band).drop i)++tail) (h116 : S.R 116 = []) (h102 : S.R 102 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareSpatialCouplingOperandsCost P q w s t u band i ∧
      Exec body prepareSpatialCouplingOperands (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          111 (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111))
          102 (List.replicate (2*band+1) tick))
          110 (cstream A w (spatialCouplingInputWords boundary t band a b i C)++S.R 110))}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := prepareSpatialCouplingCoefficients_exec (body := body)
    (NeZero.pos s) hst hP hi v S hPsrc hqsrc hsSrc htSrc husrc hbandSrc hiSrc
    h108 h115 h104 hwsrc h106 hblank h105 h116 h109 h102
  let coeffs := cstream A w (spatialCouplingCoefficientWords P q s t u band i)
  let S₁ : Stacks 117 A := {S with R := (Function.update (Function.update S.R
    111 (coeffs++S.R 111)) 102 (List.replicate (2*band+1) tick))}
  let T := if boundary then haloBoundary s t band a b else haloInterior s t band a b
  let source := cyclicPaddedLine (fun j : ZMod s => if j ∈ T then C j else 0) band
  let words := spatialCouplingInputWords boundary t band a b i C
  let rest := cstream A w ((source.drop i).drop (2*band+1))++tail
  have hwindow : words = (source.drop i).take (2*band+1) :=
    spatialCouplingInputWords_window boundary t band a b i C hi
  have hprefix : S₁.R 92 = cstream A w words++rest := by
    simp only [S₁,Function.update_of_ne (by decide : (92 : Fin 117) ≠ 102),
      Function.update_of_ne (by decide : (92 : Fin 117) ≠ 111)]
    rw [hsrc,hwindow]
    dsimp only [rest,source,T]
    rw [← List.append_assoc,← cstream_append,List.take_append_drop]
  have hlen : (cstream A w words).length = (2*band+1)*w := by
    rw [length_cstream]
    have hh := (spatialCouplingInputWords_perm boundary t band a b i C).length_eq
    simpa only [words,couplingInputWords_length] using congrArg (fun n => n*w) hh
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := copyCountedLine_exec (body := body)
    102 94 92 110 109 104 105 (by decide) (2*band+1) w
    (cstream A w words) rest hlen v₁ S₁ (by simp [S₁])
    (by simpa [S₁] using hwsrc) hprefix
    (by simpa [S₁] using h109) (by simpa [S₁] using h104) (by simpa [S₁] using h105)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by dsimp only [prepareSpatialCouplingOperandsCost]; omega,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
