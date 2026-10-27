module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedRowCoefficientPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedRowCoefficient

/-! Execute a full coefficient row by borrowing binary headers, without unary geometry loads. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- Port 113 is a retained packet in this supplier view, separate from row arithmetic. -/
def rowCoefficientFromPacket : Pr P₀ 117 Q A U :=
  .seq initializeRowCoefficientBank
    (.seq (borrowPreparedRowPacket rowCoefficientReg 113 107 109 104 105) (rowCoefficientHost indexedPreparedCoefficientRow))

def rowCoefficientFromPacketCost (P q V w band : ℕ) : ℕ :=
  (2*band*(930*P+372)+10)*tblC V w+658*V+4*w+2*((2*band+1)*w)+647

theorem rowCoefficientFromPacket_exec {P q w s t u band i : ℕ}
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = liftedCoefficientWidth P q w s t u band) (hw : (S.R 94).length = w)
    (hpacket : S.R 113 = preparedRowPacket A (liftedCoefficientWidth P q w s t u band) P q s t u band i++tail)
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = []) (h109 : S.R 109 = [])
    (hblank : ∀ r ∈ rowCoefficientPorts, S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ rowCoefficientFromPacketCost P q (liftedCoefficientWidth P q w s t u band) w band ∧
      Exec body rowCoefficientFromPacket (mk v S) m
        (mk v' {S with R := (Function.update S.R 111
          (cstream A w (spatialCouplingCoefficientWords P q s t u band i)++S.R 111))}) := by
  let V := liftedCoefficientWidth P q w s t u band
  obtain ⟨v₁,hu₁,he₁,hh₁⟩ := initializeRowCoefficientBank_exec (body := body) V w v S hV hw h106
    (fun r => hblank _ (by simpa only [mem_rowCoefficientPorts] using rowCoefficientReg_range r))
  let S₁ : Stacks 117 A := {S with R := chirpBankLoadR rowCoefficientReg (fun _ => 106) V w (fun _ => 0) S.R}
  have hoff₁ (r : Fin 117) (hr : r ∉ rowCoefficientPorts) : S₁.R r = S.R r := by
    apply chirpBankLoad_off
    exact fun k => (rowCoefficientReg_off r hr k).symm
  obtain ⟨v₂,S₂,m₂,hu₂,hm₂,he₂,hh₂,hf₂⟩ := borrowPreparedRowPacket_exec (body := body)
    rowCoefficientReg_injective 113 107 109 104 105 (by decide) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact rowCoefficientReg_off _ (by simp))
    V P q s t u band i (List.replicate V tick) (List.replicate w tick) (by simp) tail v₁ S₁ hh₁
    (by rw [hoff₁ 113 (by simp)]; exact hpacket)
    (by rw [hoff₁ 109 (by simp)]; exact h109)
    (by rw [hoff₁ 104 (by simp)]; exact h104) (by rw [hoff₁ 105 (by simp)]; exact h105)
  let st := preparedRowHeaderState (A := A) P q s t u band i
  have hc := indexedPreparedCoefficientRow_do (w := w) st
    (preparedRowHeaderState_ready P q s t u band i) hs0 hst hP hi
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := rowCoefficientHost_exec (body := body) (V := V) (w := w) indexedPreparedCoefficientRow st
    (cstream A w (spatialCouplingCoefficientWords P q s t u band i))
    hc (preparedRowHeaderState_fits P q w s t u band i hP hi) rfl
    (List.replicate V tick) (List.replicate w tick) (by simp) (by simp)
    (liftedCoefficientWidth_fits false P q w s t u band i 0 hi (Nat.zero_le band)).wordWidth v₂ S₂ hh₂
  have hoff₂ (r : Fin 117) (hr : r ∉ rowCoefficientPorts) : S₂.R r = S.R r :=
    (hf₂.2.2.2 r (rowCoefficientReg_off r hr)).trans (hoff₁ r hr)
  refine ⟨v₃,(304*V+4*w+409)+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  · have hm₃' : m₃ ≤ (2*band*(930*P+372)+10)*tblC V w+
        2*((2*band+1)*w)+130*V+133 := by simpa [V] using hm₃
    dsimp only [rowCoefficientFromPacketCost]
    dsimp only [V] at hm₂ hm₃' ⊢
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext hf₂.1 hf₂.2.1 hf₂.2.2.1 ?_
    funext r
    by_cases hr : r ∈ rowCoefficientPorts
    · have hr111 : r ≠ 111 := by intro he; subst r; simp at hr
      simp [hr,hr111,hblank r hr]
    · by_cases hr111 : r = 111
      · subst r; simp [hoff₂ 111 (by simp)]
      · simp [hr,hr111,hoff₂ r hr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
