module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthEndpointCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthMiddleCode
public import IntegerMultBounds.NLogN.PhaseCellNaturalLengths

/-! One fixed 54-atom table program emits all four candidate lengths. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalLengthCandidatesCode : TblCode 16 := naturalEndpointLengthsCode ;; naturalMiddleLengthsCode

theorem naturalLengthCandidatesCode_do {A W e s t band : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (hphase : st.val 4 = 0) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hs : 0 < s) (hst : s < t) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W e naturalLengthCandidatesCode st (fun st' =>
      st'.acc = ((naturalLengthCandidates s t band).flatMap (fun L => tblPairs A e L 0)).reverse ++ st.acc) 54 := by
  have hquot : s/(t-s)+1 < 2^W := by
    have hle := Nat.div_le_self s (t-s)
    nlinarith only [hwide, hle, hst]
  have hbandW : 2*band < 2^W := by nlinarith only [hwide]
  have he := naturalEndpointLengthsCode_do (W := W) (e := e) st hs' ht hband hphase hden hone hz hs hst hwide
  exact he.seq (K₂ := 9) (fun st₁ ⟨hp₁, ha₁, hf₁⟩ =>
    (naturalMiddleLengthsCode_do (W := W) (e := e) st₁ ((hf₁ 0 (by simp)).trans hs') hp₁
      ((hf₁ 2 (by simp)).trans hband) ((hf₁ 12 (by simp)).trans hz) hquot hbandW).mono
      (fun st₂ ha₂ => by
        rw [ha₂, ha₁]
        simp [naturalLengthCandidates, List.reverse_append, List.append_assoc]) le_rfl)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
