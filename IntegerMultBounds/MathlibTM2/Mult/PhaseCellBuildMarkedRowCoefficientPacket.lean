module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildPreparedRowPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMarkedRowCoefficient

/-! Prepare the retained self-describing coefficient packet from ordinary headers once. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def buildMarkedRowCoefficientPacket : Pr P₀ 117 Q A U :=
  .seq generateLiftedCoefficientWidth
    (.seq buildPreparedRowPacket (publishMarkedWidth 115 109 105))

def buildMarkedRowCoefficientPacketCost (P q w s t u band i : ℕ) : ℕ :=
  let V := liftedCoefficientWidth P q w s t u band
  generateLiftedCoefficientWidthCost P q w s t u band+
    buildPreparedRowPacketCost P q V w s t u band i+6*V+7

theorem buildMarkedRowCoefficientPacket_exec {P q w s t u band i : ℕ}
    (hP : 13 ≤ P) (hi : i < s) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (h115 : S.R 115 = [])
    (hwsrc : (S.R 94).length = w) (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hblank : ∀ r ∈ rowCoefficientPorts, S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ buildMarkedRowCoefficientPacketCost P q w s t u band i ∧
      Exec body buildMarkedRowCoefficientPacket (mk v S) m
        (mk v' {S with R := (Function.update S.R 109
          (markedRowCoefficientPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++S.R 109))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := generateLiftedCoefficientWidth_exec (body := body)
    P q w s t u band v S hPsrc hqsrc hwsrc hsSrc htSrc huSrc hbSrc h115 h104
    (by intro k hk
        have hk63 : k.val < 63 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        exact hblank k (by simp [hk63]))
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 115 (List.replicate V tick)}
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := buildPreparedRowPacket_exec (body := body)
    (w := w) (q := q) (P := P) (s := s) (t := t) (u := u) (band := band) (i := i)
    hP hi v₁ S₁ (by simpa [S₁] using hPsrc) (by simpa [S₁] using hqsrc)
    (by simpa [S₁] using hsSrc) (by simpa [S₁] using htSrc)
    (by simpa [S₁] using huSrc) (by simpa [S₁] using hbSrc)
    (by simpa [S₁] using hiSrc) (by simp [S₁,V]) (by simpa [S₁] using hwsrc)
    (by simpa [S₁] using h104) (by simpa [S₁] using h105) (by simpa [S₁] using h106)
    (by intro r hr
        have hr115 : r ≠ 115 := by intro h; subst r; simp at hr
        simpa [S₁,hr115] using hblank r hr)
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update S₁.R 109
    (preparedRowPacket A V P q s t u band i++S₁.R 109))}
  obtain ⟨v₃,hu₃,he₃⟩ := publishMarkedWidth_exec (body := body) 115 109 105 (by decide) v₂ S₂
    (by simpa [S₂,S₁] using h105)
  have hlen : (S₂.R 115).length = V := by simp [S₂,S₁]
  refine ⟨v₃,m₁+(m₂+(6*(S₂.R 115).length+7)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · rw [hlen]; dsimp [buildMarkedRowCoefficientPacketCost]; dsimp only [V] at *; omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext r
    by_cases h109 : r = 109 <;> by_cases hr115 : r = 115 <;>
      simp_all [S₂,S₁,V,markedRowCoefficientPacket,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
