module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputOffsetPass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputWords

/-! Generate the complete masked input row in the coefficient stream's alias-preserving order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateCouplingInputs (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (closedCouplingLookup false boundary)
    (.seq (couplingInputOffsetPass false boundary) (couplingInputOffsetPass true boundary))

def generateCouplingInputsCost (P q w s t u band a b i : ℕ) : ℕ :=
  couplingLookupRowCost P q w s t u band a b i+2*couplingInputOffsetPassCost P q w s t u band a b i

theorem generateCouplingInputsCost_eq (P q w s t u band a b i : ℕ) :
    generateCouplingInputsCost P q w s t u band a b i =
      (2*band+1)*couplingLookupRowCost P q w s t u band a b i+20*band+16 := by
  unfold generateCouplingInputsCost couplingInputOffsetPassCost couplingInputOffsetLoopCost
  ring

theorem generateCouplingInputs_exec {P q w s t u band a b i : ℕ} [NeZero s]
    (boundary : Bool) (hA : 4 ≤ A)
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
    ∃ v' m, v'.user = v.user ∧ m ≤ generateCouplingInputsCost P q w s t u band a b i ∧
      Exec body (generateCouplingInputs boundary) (mk v S) m
        (mk v' {S with R := (Function.update S.R 110
          (cstream A w (couplingInputWords boundary t band a b i C)++S.R 110))}) := by
  let zero := csyms A w (maskedCouplingInputWord false boundary t band a b i 0 C)
  let pos := cstream A w (couplingInputOffsetWords false boundary t band a b i band C)
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := closedCouplingLookup_exec (body := body)
    (P := P) (q := q) (w := w) (s := s) (t := t) (u := u) (band := band) (a := a) (b := b) (i := i) (d := 0)
    false boundary hA hst haS hbS hbandS hi (by omega) C tail v S
    hPsrc hqsrc husrc hsSrc htSrc hbandSrc hiSrc (by simp [h105]) haSrc hbSrc hwsrc
    h115 h104 h109 h106 h108 hblank hsrc
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 110 (zero++S.R 110)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := couplingInputOffsetPass_exec (body := body)
    (P := P) (q := q) (w := w) (s := s) (t := t) (u := u) (band := band) (a := a) (b := b) (i := i)
    false boundary hA hst haS hbS hbandS hi C tail v₁ S₁
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
        have hne : r ≠ 110 := by intro he; subst r; norm_num at hr
        simpa [S₁,hne] using hblank r hr) (by simpa [S₁] using hsrc) (by simpa [S₁] using h116)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 110 (pos++S₁.R 110)}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := couplingInputOffsetPass_exec (body := body)
    (P := P) (q := q) (w := w) (s := s) (t := t) (u := u) (band := band) (a := a) (b := b) (i := i)
    true boundary hA hst haS hbS hbandS hi C tail v₂ S₂
    (by simpa [S₂,S₁] using hPsrc)
    (by simpa [S₂,S₁] using hqsrc)
    (by simpa [S₂,S₁] using husrc)
    (by simpa [S₂,S₁] using hsSrc)
    (by simpa [S₂,S₁] using htSrc)
    (by simpa [S₂,S₁] using hbandSrc)
    (by simpa [S₂,S₁] using hiSrc)
    (by simpa [S₂,S₁] using h105)
    (by simpa [S₂,S₁] using haSrc)
    (by simpa [S₂,S₁] using hbSrc)
    (by simpa [S₂,S₁] using hwsrc)
    (by simpa [S₂,S₁] using h115)
    (by simpa [S₂,S₁] using h104)
    (by simpa [S₂,S₁] using h109)
    (by simpa [S₂,S₁] using h106)
    (by simpa [S₂,S₁] using h108)
    (by intro r hr
        have hne : r ≠ 110 := by intro he; subst r; norm_num at hr
        simpa [S₂,S₁,hne] using hblank r hr) (by simpa [S₂,S₁] using hsrc) (by simpa [S₂,S₁] using h116)
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · have hh := closedCouplingLookupCost_le false P q w s t u band a b i 0 (NeZero.pos s) (Nat.zero_le band)
    dsimp only [generateCouplingInputsCost]
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    · funext r
      by_cases h110 : r = 110
      · subst r
        simp [S₂,S₁,couplingInputWords_split,cstream,pos,zero,List.append_assoc,maskedCouplingInputWord]
      · simp [S₂,S₁,h110]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
