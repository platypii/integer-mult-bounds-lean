module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloEndpointLengthsCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthCandidatesCode

/-! Save the halo endpoints across ambient candidate discovery, then append
the two clipped endpoint lengths. All six candidates are computed on tape. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloLengthCandidatesCode : TblCode 16 :=
  tblBlock 16 [.copy 13 3] (.copy 14 5) ;;
    (naturalLengthCandidatesCode ;; (tblBlock 16 [.copy 3 13] (.copy 5 14) ;; haloEndpointLengthsCode))

theorem haloLengthCandidatesCode_do {A W w s t band a b : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (hphase : st.val 4 = 0) (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1)
    (hz : st.val 12 = 0) (ha : st.val 13 = a) (hb : st.val 14 = b)
    (has : a ≤ s) (hbs : b ≤ s) (hbandS : band ≤ s) (hs : 0 < s) (hst : s < t)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w haloLengthCandidatesCode st (fun st' =>
      st'.acc = ((haloLengthCandidates s t band a b).flatMap
        (fun L => tblPairs A w L 0)).reverse ++ st.acc) 133 := by
  let S₁ : TblSt 16 A := ⟨Function.update (Function.update st.val 3 a) 5 b, st.acc⟩
  have h₁ : TblDo A W w (tblBlock 16 [.copy 13 3] (.copy 14 5)) st (fun st' => st' = S₁) 2 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits]
    · simp [tblExactList,TblIns.exact,S₁,ha,hb]
  apply h₁.seq (K₂ := 131)
  intro st₁ he₁
  subst he₁
  have hn := naturalLengthCandidatesCode_frame (A := A) (W := W) (e := w) S₁
    (by simp [S₁,hs']) (by simp [S₁,ht]) (by simp [S₁,hband])
    (by simp [S₁,hphase]) (by simp [S₁,hden]) (by simp [S₁,hone]) (by simp [S₁,hz]) hs hst hwide
  apply hn.seq (K₂ := 77)
  intro st₂ ⟨hacc₂,hf₂⟩
  let S₃ : TblSt 16 A := ⟨Function.update (Function.update st₂.val 13 a) 14 b, st₂.acc⟩
  have hrestore : TblDo A W w (tblBlock 16 [.copy 3 13] (.copy 5 14)) st₂ (fun st' => st' = S₃) 2 := by
    apply TblDo.block
    · simp [tblFitsList,TblIns.fits]
    · simp [tblExactList,TblIns.exact,S₃,hf₂ 3 (by simp),hf₂ 5 (by simp),S₁]
  apply hrestore.seq (K₂ := 75)
  intro st₃ he₃
  subst he₃
  exact (haloEndpointLengthsCode_do (A := A) (W := W) (w := w) S₃
    (by simp [S₃,hf₂ 0 (by simp),S₁,hs'])
    (by simp [S₃,hf₂ 2 (by simp),S₁,hband])
    (by simp [S₃,hf₂ 6 (by simp),S₁,hden])
    (by simp [S₃,hf₂ 7 (by simp),S₁,hone])
    (by simp [S₃,hf₂ 12 (by simp),S₁,hz]) (by simp [S₃]) (by simp [S₃])
    has hbs hbandS hs hst hwide).mono (fun st₄ ⟨hout,_⟩ => by
      rw [hout]
      simp [S₃,hacc₂,S₁,haloLengthCandidates,List.flatMap_append,List.reverse_append,List.append_assoc]) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
