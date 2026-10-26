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

theorem naturalLengthCandidatesCode_frame {A W e s t band : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (hphase : st.val 4 = 0) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hs : 0 < s) (hst : s < t) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W e naturalLengthCandidatesCode st (fun st' =>
      st'.acc = ((naturalLengthCandidates s t band).flatMap (fun L => tblPairs A e L 0)).reverse ++ st.acc ∧
      ∀ k, k ∉ [(4 : Fin 16),8,9,10,11,13,14] → st'.val k = st.val k) 54 := by
  have hquot : s/(t-s)+1 < 2^W := by
    have hle := Nat.div_le_self s (t-s)
    nlinarith only [hwide, hle, hst]
  have hbandW : 2*band < 2^W := by nlinarith only [hwide]
  have he := naturalEndpointLengthsCode_do (W := W) (e := e) st hs' ht hband hphase hden hone hz hs hst hwide
  exact he.seq (K₂ := 9) (fun st₁ ⟨hp₁, ha₁, hf₁⟩ =>
    (naturalMiddleLengthsCode_frame (W := W) (e := e) st₁ ((hf₁ 0 (by simp)).trans hs') hp₁
      ((hf₁ 2 (by simp)).trans hband) ((hf₁ 12 (by simp)).trans hz) hquot hbandW).mono
      (fun st₂ ⟨ha₂,hf₂⟩ => by
        constructor
        · rw [ha₂, ha₁]
          simp [naturalLengthCandidates, List.reverse_append, List.append_assoc]
        · intro k hk
          have h₁ : k ∉ [(4 : Fin 16),8,9,10,11] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at *
            tauto
          have h₂ : k ∉ [(11 : Fin 16),13,14] := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at *
            tauto
          exact (hf₂ k h₂).trans (hf₁ k h₁)) le_rfl)

theorem naturalLengthCandidatesCode_do {A W e s t band : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (hphase : st.val 4 = 0) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hs : 0 < s) (hst : s < t) (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W e naturalLengthCandidatesCode st (fun st' =>
      st'.acc = ((naturalLengthCandidates s t band).flatMap (fun L => tblPairs A e L 0)).reverse ++ st.acc) 54 :=
  (naturalLengthCandidatesCode_frame st hs' ht hband hphase hden hone hz hs hst hwide).mono
    (fun _ h => h.1) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
