module

public import IntegerMultBounds.MathlibTM2.Fast.TableBounds
public import IntegerMultBounds.MathlibTM2.Fast.TableNatSub

/-! Compute and emit the two possible un-clipped interior lengths with nine
checked table atoms. Truncated subtraction handles empty interiors directly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def naturalMiddleLengthsCode : TblCode 16 :=
  tblBlock 16 [.div 0 4 13] (.add 2 2 14) ;;
    (tblNatSub 13 14 11 ;; (.ins (.emit 11 12) ;;
      (.ins (.inc 13) ;; (tblNatSub 13 14 11 ;; .ins (.emit 11 12)))))

theorem naturalMiddleLengthsCode_frame {A W e s d band : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hd : st.val 4 = d) (hband : st.val 2 = band) (hz : st.val 12 = 0)
    (hquot : s/d+1 < 2^W) (hbandW : 2*band < 2^W) :
    TblDo A W e naturalMiddleLengthsCode st (fun st' =>
      st'.acc = (tblPairs A e (s/d-2*band) 0 ++ tblPairs A e ((s/d+1)-2*band) 0).reverse ++ st.acc ∧
      ∀ k, k ∉ [(11 : Fin 16),13,14] → st'.val k = st.val k) 9 := by
  let S₁ : TblSt 16 A := ⟨Function.update (Function.update st.val 13 (s/d)) 14 (2*band), st.acc⟩
  have h₁ : TblDo A W e (tblBlock 16 [.div 0 4 13] (.add 2 2 14)) st (fun st' => st' = S₁) 2 := by
    apply TblDo.block
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hs, hd, hband]
      omega
    · simp [tblExactList, TblIns.exact, S₁, hs, hd, hband, two_mul]
  let S₂ : TblSt 16 A := ⟨Function.update S₁.val 11 (s/d-2*band), st.acc⟩
  have h₂ : TblDo A W e (tblNatSub 13 14 11) S₁ (fun st' => st' = S₂) 2 := by
    simpa [S₂, S₁] using tblNatSub_do (A := A) (W := W) (w := e) 13 14 11 S₁ (by simp [S₁]; omega)
  let S₃ := (TblIns.emit 11 12).run A W e S₂
  have h₃ : TblDo A W e (.ins (.emit 11 12)) S₂ (fun st' => st' = S₃) 1 := TblDo.ins _ (by rfl)
  let S₄ : TblSt 16 A := ⟨Function.update S₃.val 13 (s/d+1), S₃.acc⟩
  have h₄ : TblDo A W e (.ins (.inc 13)) S₃ (fun st' => st' = S₄) 1 := by
    apply TblDo.insX
    · simpa [TblIns.fits, S₃, S₂, S₁, TblIns.run] using hquot
    · simp [TblIns.exact, S₄, S₃, S₂, S₁, TblIns.run]
  let S₅ : TblSt 16 A := ⟨Function.update S₄.val 11 ((s/d+1)-2*band), S₄.acc⟩
  have h₅ : TblDo A W e (tblNatSub 13 14 11) S₄ (fun st' => st' = S₅) 2 := by
    simpa [S₅, S₄, S₃, S₂, S₁, TblIns.run, Function.update_idem] using
      tblNatSub_do (A := A) (W := W) (w := e) 13 14 11 S₄ (by simp [S₄]; exact hquot)
  let S₆ := (TblIns.emit 11 12).run A W e S₅
  have h₆ : TblDo A W e (.ins (.emit 11 12)) S₅ (fun st' => st' = S₆) 1 := TblDo.ins _ (by rfl)
  have hc := h₁.seq (fun st' he => he ▸ h₂.seq (fun st'' he' => he' ▸ h₃.seq
    (fun st₃ he₃ => he₃ ▸ h₄.seq (fun st₄ he₄ => he₄ ▸ h₅.seq (fun st₅ he₅ => he₅ ▸ h₆)))))
  exact hc.mono (fun st' he => by
    subst he
    constructor
    · simp [S₆, S₅, S₄, S₃, S₂, S₁, TblIns.run, hz, List.reverse_append, List.append_assoc]
    · intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
      simp [S₆, S₅, S₄, S₃, S₂, S₁, TblIns.run, hk.1, hk.2.1, hk.2.2]) (by decide)

theorem naturalMiddleLengthsCode_do {A W e s d band : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hd : st.val 4 = d) (hband : st.val 2 = band) (hz : st.val 12 = 0)
    (hquot : s/d+1 < 2^W) (hbandW : 2*band < 2^W) :
    TblDo A W e naturalMiddleLengthsCode st (fun st' =>
      st'.acc = (tblPairs A e (s/d-2*band) 0 ++ tblPairs A e ((s/d+1)-2*band) 0).reverse ++ st.acc) 9 :=
  (naturalMiddleLengthsCode_frame st hs hd hband hz hquot hbandW).mono (fun _ h => h.1) le_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
