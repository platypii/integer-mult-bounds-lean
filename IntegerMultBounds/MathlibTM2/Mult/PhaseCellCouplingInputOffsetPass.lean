module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputOffsetLoop

/-! Generate and retire the input-pass controls; only the gathered input prefix changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def couplingInputOffsetPass (negative boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (ucopy 100 116 109) (.seq (couplingInputOffsetLoop negative boundary) (uclear 105))

def couplingInputOffsetPassCost (P q w s t u band a b i : ℕ) : ℕ :=
  couplingInputOffsetLoopCost P q w s t u band a b i+6*band+6

theorem couplingInputOffsetPass_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (negative boundary : Bool) (hA : 4 ≤ A)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s) (hi : i < s)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q) (husrc : (S.R 99).length = u)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (hbandSrc : (S.R 100).length = band) (hiSrc : (S.R 107).length = i) (h105 : S.R 105 = [])
    (haSrc : (S.R 101).length = a) (hbSrc : (S.R 103).length = b)
    (hwsrc : (S.R 94).length = w) (h115 : S.R 115 = []) (h104 : S.R 104 = [])
    (h109 : S.R 109 = []) (h106 : S.R 106 = []) (h108 : S.R 108 = [])
    (hblank : ∀ r : Fin 117, r.val < 31 → S.R r = [])
    (hsrc : S.R 92 = cstream A w (chirpLine s C)++tail) (h116 : S.R 116 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingInputOffsetPassCost P q w s t u band a b i ∧
      Exec body (couplingInputOffsetPass negative boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (cstream A w (couplingInputOffsetWords negative boundary t band a b i band C)++S.R 110))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 100) (b := 116) (t := 109)
    (by decide) (by decide) (by decide) v S h109
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 116 (List.replicate band tick)}
  have he₁' : Exec body (ucopy 100 116 109) (mk v S) (4*band+4) (mk v₁ S₁) := by
    simpa [S₁,hbandSrc,h116] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := couplingInputOffsetLoop_exec (body := body)
    (P := P) (q := q) (w := w) (s := s) (t := t) (u := u) (band := band) (a := a) (b := b) (i := i)
    negative boundary hA hst haS hbS hbandS hi C tail v₁ S₁
    (by simpa [S₁] using hPsrc)
    (by simpa [S₁] using hqsrc)
    (by simpa [S₁] using husrc)
    (by simpa [S₁] using hsSrc)
    (by simpa [S₁] using htSrc)
    (by simpa [S₁] using hbandSrc)
    (by simpa [S₁] using hiSrc)
    (by simpa [S₁] using h105)
    (by simpa [S₁] using haSrc)
    (by simpa [S₁] using hbSrc)
    (by simpa [S₁] using hwsrc)
    (by simpa [S₁] using h115)
    (by simpa [S₁] using h104)
    (by simpa [S₁] using h109)
    (by simpa [S₁] using h106)
    (by simpa [S₁] using h108)
    (by intro r hr
        have hne : r ≠ 116 := by intro he; subst r; norm_num at hr
        simpa [S₁,hne] using hblank r hr) (by simpa [S₁] using hsrc) (by simp [S₁])
  let words := cstream A w (couplingInputOffsetWords negative boundary t band a b i band C)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update (Function.update (Function.update S₁.R
    105 (List.replicate band tick)) 110 (words++S₁.R 110)) 116 []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 105 v₂ S₂
  have he₃' : Exec body (uclear 105) (mk v₂ S₂) (2*band+2)
      (mk v₃ {S with R := Function.update S.R 110 (words++S.R 110)}) := by
    convert he₃ using 1
    · simp [S₂]
    · apply congrArg (mk v₃)
      refine Stacks.ext ?_ ?_ ?_ ?_
      · rfl
      · rfl
      · rfl
      · funext r
        by_cases h105' : r = 105 <;> by_cases h110 : r = 110 <;> by_cases h116' : r = 116 <;>
          simp [S₂,S₁,h105',h110,h116',h105,h116]
  refine ⟨v₃,(4*band+4)+(m₂+(2*band+2)),hu₃.trans (hu₂.trans hu₁),?_,
    Exec.seq he₁' (Exec.seq he₂ he₃')⟩
  dsimp only [couplingInputOffsetPassCost]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
