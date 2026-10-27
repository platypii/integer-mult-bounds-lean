module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateCouplingCoefficients
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSpatialCouplingWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversePrefixInPlace

/-! Generate a complete alias-preserving coefficient row from ordinary headers.
Only the row prefix changes; all offset counters and table banks restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateSpatialCouplingCoefficients : Pr P₀ 117 Q A U :=
  .seq (coefficientOffsetPass false)
    (.seq (reversePrefixInPlace 100 104 94 111 115 105 106 108 109)
      (.seq (appendSelectedCoefficient false) (coefficientOffsetPass true)))

def generateSpatialCouplingCoefficientsCost (P q w s t u band i : ℕ) : ℕ :=
  generateCouplingCoefficientsCost P q w s t u band i +32*band*w+28*band+22

theorem generateSpatialCouplingCoefficients_exec {w q P s t u band i : ℕ}
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (h108 : S.R 108 = [])
    (h115 : S.R 115 = []) (h104 : S.R 104 = []) (hwsrc : (S.R 94).length = w) (h106 : S.R 106 = [])
    (hblank : ∀ r : Fin 117, r.val < 63 → S.R r = [])
    (h105 : S.R 105 = []) (h116 : S.R 116 = []) (h109 : S.R 109 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateSpatialCouplingCoefficientsCost P q w s t u band i ∧
      Exec body generateSpatialCouplingCoefficients (mk v S) m
        (mk v' {S with R := (Function.update S.R 111
          (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111))}) := by
  let pos := offsetCoefficientWords false P q s t u band i band
  let zero := csyms A w (signedCoefficientWord false P q s t u band i 0)
  have hpos : pos.length = band := by simp [pos,offsetCoefficientWords]
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := coefficientOffsetPass_exec (body := body)
    (w := w) (q := q) (P := P) (s := s) (t := t) (u := u) (band := band) (i := i)
    false hs0 hst hP hi v S hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc h108
    h115 h104 hwsrc h106 hblank h116 h109
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 111 (cstream A w pos++S.R 111)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := reversePrefixInPlace_exec (body := body)
    (records := 100) (recordSaved := 104) (width := 94) (src := 111) (dst := 115)
    (saved := 105) (buf := 106) (tmp := 108) (count := 109)
    (by decide) w pos (S.R 111) v₁ S₁
    (by simpa [S₁,hpos] using hbSrc) (by simpa [S₁] using hwsrc) (by simp [S₁])
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [S₁,h104,h115,h105,h106,h108,h109])
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 111 (cstream A w pos.reverse++S.R 111)}
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := appendSelectedCoefficient_exec (body := body)
    (w := w) (q := q) (P := P) (s := s) (t := t) (u := u) (band := band) (i := i)
    (d := 0) false hs0 hst hP (by omega) hi v₂ S₂
    (by simpa [S₂,S₁] using hPsrc)
    (by simpa [S₂,S₁] using hqsrc)
    (by simpa [S₂,S₁] using hsSrc)
    (by simpa [S₂,S₁] using htSrc)
    (by simpa [S₂,S₁] using huSrc)
    (by simpa [S₂,S₁] using hbSrc)
    (by simpa [S₂,S₁] using hiSrc)
    (by simpa [S₂,S₁] using h108)
    (by simpa [S₂,S₁] using h115)
    (by simpa [S₂,S₁] using h104)
    (by simpa [S₂,S₁] using hwsrc)
    (by simpa [S₂,S₁] using h106)
    (by intro r hr
        have hne : r ≠ 111 := by intro he; subst r; norm_num at hr
        simpa [S₂,S₁,hne] using hblank r hr)
  let S₃ : Stacks 117 A := {S₂ with R := Function.update S₂.R 111 (zero++S₂.R 111)}
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := coefficientOffsetPass_exec (body := body)
    (w := w) (q := q) (P := P) (s := s) (t := t) (u := u) (band := band) (i := i)
    true hs0 hst hP hi v₃ S₃
    (by simpa [S₃,S₂,S₁] using hPsrc)
    (by simpa [S₃,S₂,S₁] using hqsrc)
    (by simpa [S₃,S₂,S₁] using hsSrc)
    (by simpa [S₃,S₂,S₁] using htSrc)
    (by simpa [S₃,S₂,S₁] using huSrc)
    (by simpa [S₃,S₂,S₁] using hbSrc)
    (by simpa [S₃,S₂,S₁] using hiSrc)
    (by simpa [S₃,S₂,S₁] using h108)
    (by simpa [S₃,S₂,S₁] using h115)
    (by simpa [S₃,S₂,S₁] using h104)
    (by simpa [S₃,S₂,S₁] using hwsrc)
    (by simpa [S₃,S₂,S₁] using h106)
    (by intro r hr
        have hne : r ≠ 111 := by intro he; subst r; norm_num at hr
        simpa [S₃,S₂,S₁,hne] using hblank r hr)
    (by simpa [S₃,S₂,S₁] using h116)
    (by simpa [S₃,S₂,S₁] using h109)
  refine ⟨v₄,m₁+(m₂+(m₃+m₄)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · dsimp only [generateSpatialCouplingCoefficientsCost,generateCouplingCoefficientsCost]
    rw [hpos] at hm₂
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h111 : r = 111
    · subst r
      simp [S₃,S₂,S₁,spatialCouplingCoefficientWords_split,cstream,pos,zero,List.append_assoc]
    · simp [S₃,S₂,S₁,h111]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
