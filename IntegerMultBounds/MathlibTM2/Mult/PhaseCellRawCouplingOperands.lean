module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingOperands
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCaptureCouplingSource

/-! Prepare coupling operands directly from the ambient input and release its snapshot. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def rawCouplingOperands (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq captureCouplingSource (.seq (prepareCouplingOperands boundary) (uclear 92))

def rawCouplingOperandsCost (P q w s t u band a b i : ℕ) : ℕ :=
  s*(16*w+9)+16+prepareCouplingOperandsCost P q w s t u band a b i+2*(s*w)+2

theorem rawCouplingOperands_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 4 ≤ A)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s) (hP : 13 ≤ P)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (hsrc : S.R 110 = cstream A w (chirpLine s C)++tail) (h92 : S.R 92 = []) (h116 : S.R 116 = []) (h102 : S.R 102 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ rawCouplingOperandsCost P q w s t u band a b i ∧
      Exec body (rawCouplingOperands boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          111 (cstream A w (couplingCoefficientWords P q s t u band i)++S.R 111))
          102 (List.replicate (2*band+1) tick))
          110 (cstream A w (couplingInputWords boundary t band a b i C)++S.R 110))}) := by
  let source := cstream A w (chirpLine s C)
  have hlen : source.length = s*w := by simp [source,chirpLine]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := captureCouplingSource_exec (body := body)
    s w source tail v S hsSrc hwsrc hsrc hlen h92 h109 h104 h105
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 92 source}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := prepareCouplingOperands_exec (body := body)
    (P := P) (q := q) (w := w) (s := s) (t := t) (u := u) (band := band) (a := a) (b := b) (i := i)
    boundary hA hst haS hbS hbandS hi hP C [] v₁ S₁
    (by simpa [S₁] using hPsrc) (by simpa [S₁] using hqsrc)
    (by simpa [S₁] using husrc) (by simpa [S₁] using hsSrc)
    (by simpa [S₁] using htSrc) (by simpa [S₁] using hbandSrc)
    (by simpa [S₁] using hiSrc) (by simpa [S₁] using h105)
    (by simpa [S₁] using haSrc) (by simpa [S₁] using hbSrc)
    (by simpa [S₁] using hwsrc) (by simpa [S₁] using h115)
    (by simpa [S₁] using h104) (by simpa [S₁] using h109)
    (by simpa [S₁] using h106) (by simpa [S₁] using h108)
    (by intro r hr
        have hne : r ≠ 92 := by intro he; subst r; norm_num at hr
        simpa [S₁,hne] using hblank r hr)
    (by simp [S₁,source]) (by simpa [S₁] using h116) (by simpa [S₁] using h102)
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update (Function.update (Function.update S₁.R
    111 (cstream A w (couplingCoefficientWords P q s t u band i)++S₁.R 111))
    102 (List.replicate (2*band+1) tick))
    110 (cstream A w (couplingInputWords boundary t band a b i C)++S₁.R 110))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 92 v₂ S₂
  refine ⟨v₃,m₁+(m₂+(2*(s*w)+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by simp [S₂,S₁,hlen]) ?_⟩
  · dsimp only [rawCouplingOperandsCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h : r = 92 <;> simp [S₂,S₁,h,h92,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
