module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishPreparedRowPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRowConstants

/-! Convert ordinary geometry and prepare pi and scaling powers once, then publish and release. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def buildPreparedRowPacket : Pr P₀ 117 Q A U :=
  .seq initializeRowCoefficientHeaders (.seq (tblHost rowCoefficientReg prepareRowConstants 111)
    (.seq (publishPreparedRowPacket rowCoefficientReg 109 104 105) (clearWords rowCoefficientPorts)))

def buildPreparedRowPacketCost (P q V w s t u band i : ℕ) : ℕ :=
  initializeRowCoefficientHeadersCost P q V w s t u band i+
    (154*P+4*q+413)*tblC V w+240*V+244

theorem buildPreparedRowPacket_exec {P q w s t u band i : ℕ}
    (hP : 13 ≤ P) (hi : i < s) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hPsrc : (S.R 114).length = P) (hqsrc : (S.R 112).length = q)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t)
    (huSrc : (S.R 99).length = u) (hbSrc : (S.R 100).length = band)
    (hiSrc : (S.R 107).length = i)
    (hVsrc : (S.R 115).length = liftedCoefficientWidth P q w s t u band) (hwsrc : (S.R 94).length = w)
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = [])
    (hblank : ∀ r ∈ rowCoefficientPorts, S.R r = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ buildPreparedRowPacketCost P q (liftedCoefficientWidth P q w s t u band) w s t u band i ∧
      Exec body buildPreparedRowPacket (mk v S) m
        (mk v' {S with R := (Function.update S.R 109
          (preparedRowPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++S.R 109))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  have hw : w ≤ V := (liftedCoefficientWidth_fits false P q w s t u band i 0 hi (by omega)).wordWidth
  obtain ⟨v₁,S₁,m₁,hu₁,hm₁,he₁,hh₁,hf₁⟩ := initializeRowCoefficientHeaders_exec (body := body)
    v S hPsrc hqsrc hsSrc htSrc huSrc hbSrc hiSrc hVsrc hwsrc h106 hblank
  let st := rowCoefficientHeaderState (A := A) P q s t u band i
  have hc := prepareRowConstants_do (P := P) (q := q) (w := w) (s := s) (t := t)
    (u := u) (band := band) (i := i) st
    (by simp [st,rowCoefficientHeaderState]) (by simp [st,rowCoefficientHeaderState])
    (by simp [st,rowCoefficientHeaderState]) (by simp [st,rowCoefficientHeaderState])
    (by simp [st,rowCoefficientHeaderState]) (by simp [st,rowCoefficientHeaderState])
    (by simp [st,rowCoefficientHeaderState]) hP hi
  obtain ⟨v₂,S₂,m₂,st',hp₂,hu₂,hm₂,he₂,ho₂,hh₂,hin₂,hout₂,hl₂,hf₂⟩ := tblHost_runs (body := body)
    rowCoefficientReg_injective (rowCoefficientReg_off 111 (by simp))
    (List.replicate V tick) (List.replicate w tick) (by simp) (by simp) hw hc
    (rowCoefficientHeaderState_fits P q w s t u band i hi) v₁ S₁ hh₁
  have hacc : st'.acc = [] := by simpa [st,rowCoefficientHeaderState] using hp₂.2.2
  have hst' : (⟨st'.val,[]⟩ : TblSt 50 A) = st' := by cases st'; simp_all
  have hoff (r : Fin 117) (hr : r ∉ rowCoefficientPorts) : S₂.R r = S.R r := by
    have hbase := hf₁.2.2.2 r (rowCoefficientReg_off r hr)
    by_cases h111 : r = 111
    · subst r
      have ho : S₂.R 111 = S₁.R 111 := by simpa only [hacc,List.reverse_nil,List.nil_append] using ho₂
      exact ho.trans hbase
    · exact (hf₂ r h111 (rowCoefficientReg_off r hr)).trans hbase
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := publishPreparedRowPacket_exec (body := body)
    rowCoefficientReg_injective 109 104 105 (by decide) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact rowCoefficientReg_off _ (by simp))
    V P q s t u band i (List.replicate V tick) (List.replicate w tick) (by simp) st' hp₂.1 hp₂.2.1 v₂ S₂
    (by simpa only [hst'] using hh₂)
    (by rw [hoff 104 (by simp)]; exact h104) (by rw [hoff 105 (by simp)]; exact h105)
  let S₃ : Stacks 117 A := {S₂ with R := (Function.update S₂.R 109
    (preparedRowPacket A V P q s t u band i++S₂.R 109))}
  have hh₃ : tblHolds rowCoefficientReg S₃ (tblRho V (List.replicate V tick) (List.replicate w tick)
      ⟨st'.val,[]⟩) := by
    intro r
    simpa [S₃,rowCoefficientReg_off 109 (by simp) r] using hh₂ r
  obtain ⟨v₄,m₄,hu₄,hm₄,he₄⟩ := clearRowCoefficientBank_exec (body := body) V w st'.val
    (List.replicate V tick) (List.replicate w tick) (by simp) (by simp) hw v₃ S₃ hh₃
  refine ⟨v₄,m₁+(m₂+(m₃+m₄)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · rw [hacc] at hm₂
    dsimp only [buildPreparedRowPacketCost]; dsimp only [V] at *; simp only [List.length_nil] at hm₂
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext (hin₂.trans hf₁.1) (hout₂.trans hf₁.2.1) (hl₂.trans hf₁.2.2.1) ?_
    funext r
    by_cases hr : r ∈ rowCoefficientPorts
    · have hr109 : r ≠ 109 := by intro h; subst r; simp at hr
      simp [hr,hr109,hblank r hr]
    · by_cases hr109 : r = 109
      · subst r; simp [S₃,V,hoff 109 (by simp)]
      · simp [S₃,hr,hr109,hoff r hr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
