module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowCoefficientPacket

/-! Convert ordinary row geometry once, publish its binary packet, and release the table bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def buildRowCoefficientPacket : Pr P₀ 117 Q A U :=
  .seq initializeRowCoefficientHeaders
    (.seq (publishRowCoefficientPacket rowCoefficientReg 109 104 105) (clearWords rowCoefficientPorts))

def buildRowCoefficientPacketCost (P q V w s t u band i : ℕ) : ℕ :=
  initializeRowCoefficientHeadersCost P q V w s t u band i+200*V+202

theorem buildRowCoefficientPacket_exec {V w q P s t u band i : ℕ}
    (hw : w ≤ V) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i) (hVsrc : (S.R 115).length = V) (hwsrc : (S.R 94).length = w)
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hblank : ∀ r ∈ rowCoefficientPorts, S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ buildRowCoefficientPacketCost P q V w s t u band i ∧
      Exec body buildRowCoefficientPacket (mk v S) m
        (mk v' {S with R := Function.update S.R 109 (rowCoefficientPacket A V P q s t u band i++S.R 109)}) := by
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hh₁,hf₁⟩ := initializeRowCoefficientHeaders_exec (body := body)
    v S hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc hVsrc hwsrc h106 hblank
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := publishRowCoefficientPacket_exec (body := body) rowCoefficientReg_injective
    109 104 105 (by decide) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact rowCoefficientReg_off _ (by simp))
    V P q s t u band i (List.replicate V tick) (List.replicate w tick) (by simp) v₁ S₁ hh₁
    (by rw [hf₁.2.2.2 104 (rowCoefficientReg_off 104 (by simp))]; exact h104)
    (by rw [hf₁.2.2.2 105 (rowCoefficientReg_off 105 (by simp))]; exact h105)
  let S₂ : Stacks 117 A := {S₁ with R := (Function.update S₁.R 109
    (rowCoefficientPacket A V P q s t u band i++S₁.R 109))}
  have hh₂ : tblHolds rowCoefficientReg S₂ (tblRho V (List.replicate V tick) (List.replicate w tick)
      (rowCoefficientHeaderState P q s t u band i)) := by
    intro r
    simpa [S₂,rowCoefficientReg_off 109 (by simp) r] using hh₁ r
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := clearRowCoefficientBank_exec (body := body) V w
    (rowCoefficientHeaderState (A := A) P q s t u band i).val
    (List.replicate V tick) (List.replicate w tick) (by simp) (by simp) hw v₂ S₂ hh₂
  refine ⟨v₃,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),
    by dsimp only [buildRowCoefficientPacketCost]; omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext hf₁.1 hf₁.2.1 hf₁.2.2.1 ?_
  funext r
  by_cases hr : r ∈ rowCoefficientPorts
  · have hr109 : r ≠ 109 := by intro he; subst r; simp at hr
    simp [hr,hr109,hblank r hr]
  · have hoff := hf₁.2.2.2 r (rowCoefficientReg_off r hr)
    by_cases hr109 : r = 109
    · subst r; simp [S₂,hoff]
    · simp [S₂,hr,hr109,hoff]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
