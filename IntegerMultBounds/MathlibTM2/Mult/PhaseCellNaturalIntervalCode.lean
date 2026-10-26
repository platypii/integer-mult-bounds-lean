module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLowerCode
public import IntegerMultBounds.NLogN.PhaseCellNaturalEndpoints

/-! A fixed table program computes the exact original phase-cell origin and
length using 21 atoms, with clipped and empty cells handled structurally. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalIntervalCode : TblCode 16 :=
  tblBlock 16 [.mul 0 4 8] (.add 8 8 8) ;;
    (naturalLowerCode 9 ;; (.ins (.add 9 2 9) ;;
      (tblBlock 16 [.add 8 0 8] (.add 8 0 8) ;; (naturalLowerCode 10 ;;
        (tblNatMin 0 10 10 ;; (tblNatSub 10 2 10 ;; tblNatSub 10 9 11))))))

theorem naturalIntervalWideCode_do {A W w s t band phase : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hphase : st.val 4 = phase)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1)
    (_hs : 0 < s) (hst : s < t) (hphaseMax : phase ≤ 2*(t-s)+1)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w naturalIntervalCode st (fun st' =>
      st'.val 9 = naturalStart s t band phase ∧ st'.val 10 = naturalStop s t band phase ∧
      st'.val 11 = naturalLength s t band phase ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(8 : Fin 16), 9, 10, 11] → st'.val k = st.val k) 21 := by
  have hd : 0 < t-s := by omega
  have hprod : s*(phase+1) ≤ 2*t*(t+1) := by
    have hd := Nat.sub_le t s
    nlinarith only [hphaseMax, hst.le, hd]
  have hdle : t-s ≤ t := Nat.sub_le _ _
  have hcalc : 2*s*(phase+1)+2*(t-s)+band+2 < 2^W := by nlinarith only [hwide, hprod, hdle]
  have hlo (p : ℕ) : phaseLower s (t-s) p ≤ 2*s*p+2*(t-s) := by
    unfold phaseLower
    exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have hsW : s < 2^W := by nlinarith only [hcalc]
  let S₁ : TblSt 16 A := ⟨Function.update st.val 8 (2*s*phase), st.acc⟩
  have h₁ : TblDo A W w (tblBlock 16 [.mul 0 4 8] (.add 8 8 8)) st (fun st' => st' = S₁) 2 := by
    apply TblDo.block
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hs', hphase]
      constructor <;> nlinarith only [hcalc]
    · simp [tblExactList, TblIns.exact, S₁, hs', hphase, Function.update_idem]
      congr 1
      ring
  let S₂ : TblSt 16 A := ⟨Function.update S₁.val 9 (phaseLower s (t-s) phase), st.acc⟩
  have h₂ : TblDo A W w (naturalLowerCode 9) S₁ (fun st' => st' = S₂) 5 := by
    simpa only [S₂, phaseLower] using naturalLowerCode_do (A := A) (W := W) (w := w) 9 (by decide) S₁
      (by simp [S₁, hs']) (by simp [S₁, hden]) (by simp [S₁, hone]) (by simp [S₁]) hd
      (by nlinarith only [hcalc])
  let S₃ : TblSt 16 A := ⟨Function.update S₂.val 9 (naturalStart s t band phase), st.acc⟩
  have h₃ : TblDo A W w (.ins (.add 9 2 9)) S₂ (fun st' => st' = S₃) 1 := by
    apply TblDo.insX
    · simp [TblIns.fits, S₂, S₁, hband]
      have hh := hlo phase
      nlinarith only [hcalc, hh]
    · simp [TblIns.exact, S₃, S₂, S₁, naturalStart, hband, Function.update_idem]
  let S₄ : TblSt 16 A := ⟨Function.update S₃.val 8 (2*s*(phase+1)), st.acc⟩
  have h₄ : TblDo A W w (tblBlock 16 [.add 8 0 8] (.add 8 0 8)) S₃ (fun st' => st' = S₄) 2 := by
    apply TblDo.block
    · simp [tblFitsList, TblIns.fits, TblIns.exact, S₃, S₂, S₁, hs']
      constructor <;> nlinarith only [hcalc]
    · simp [tblExactList, TblIns.exact, S₄, S₃, S₂, S₁, hs', Function.update_idem]
      congr 1
      ring
  let S₅ : TblSt 16 A := ⟨Function.update S₄.val 10 (phaseLower s (t-s) (phase+1)), st.acc⟩
  have h₅ : TblDo A W w (naturalLowerCode 10) S₄ (fun st' => st' = S₅) 5 := by
    simpa only [S₅, phaseLower] using naturalLowerCode_do (A := A) (W := W) (w := w) 10 (by decide) S₄
      (by simp [S₄, S₃, S₂, S₁, hs']) (by simp [S₄, S₃, S₂, S₁, hden])
      (by simp [S₄, S₃, S₂, S₁, hone]) (by simp [S₄]) hd (by omega)
  let S₆ : TblSt 16 A := ⟨Function.update S₅.val 10 (min s (phaseLower s (t-s) (phase+1))), st.acc⟩
  have h₆ : TblDo A W w (tblNatMin 0 10 10) S₅ (fun st' => st' = S₆) 2 := by
    simpa [S₆, S₅, S₄, S₃, S₂, S₁, hs', Function.update_idem] using
      tblNatMin_do (A := A) (W := W) (w := w) 0 10 10 S₅
  let S₇ : TblSt 16 A := ⟨Function.update S₆.val 10 (naturalStop s t band phase), st.acc⟩
  have h₇ : TblDo A W w (tblNatSub 10 2 10) S₆ (fun st' => st' = S₇) 2 := by
    have hh : S₆.val 10 < 2^W := by simpa [S₆] using (min_le_left s (phaseLower s (t-s) (phase+1))).trans_lt hsW
    simpa [S₇, S₆, S₅, S₄, S₃, S₂, S₁, naturalStop, hband, Function.update_idem] using
      tblNatSub_do (A := A) (W := W) (w := w) 10 2 10 S₆ hh
  let S₈ : TblSt 16 A := ⟨Function.update S₇.val 11 (naturalLength s t band phase), st.acc⟩
  have h₈ : TblDo A W w (tblNatSub 10 9 11) S₇ (fun st' => st' = S₈) 2 := by
    have hh : S₇.val 10 < 2^W := by simpa [S₇] using (naturalStop_le s t band phase).trans_lt hsW
    simpa [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, naturalLength, Function.update_idem] using
      tblNatSub_do (A := A) (W := W) (w := w) 10 9 11 S₇ hh
  have hc := h₁.seq (fun st' he => he ▸ h₂.seq (fun st'' he' => he' ▸ h₃.seq
    (fun st''' he'' => he'' ▸ h₄.seq (fun st₄ he₄ => he₄ ▸ h₅.seq (fun st₅ he₅ => he₅ ▸ h₆.seq
      (fun st₆ he₆ => he₆ ▸ h₇.seq (fun st₇ he₇ => he₇ ▸ h₈)))))))
  refine hc.mono (fun st' he => he ▸ ?_) (by decide)
  refine ⟨by simp [S₈, S₇, S₆, S₅, S₄, S₃], by simp [S₈, S₇], by simp [S₈], rfl, ?_⟩
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
  simp [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2]

theorem naturalIntervalCode_do {A W w s t band phase : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hphase : st.val 4 = phase)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1)
    (hs : 0 < s) (hst : s < t) (hphaseMax : phase ≤ t-s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) :
    TblDo A W w naturalIntervalCode st (fun st' =>
      st'.val 9 = naturalStart s t band phase ∧ st'.val 10 = naturalStop s t band phase ∧
      st'.val 11 = naturalLength s t band phase ∧ st'.acc = st.acc ∧
      ∀ k, k ∉ [(8 : Fin 16), 9, 10, 11] → st'.val k = st.val k) 21 :=
  naturalIntervalWideCode_do st hs' hband hphase hden hone hs hst (by omega) hwide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
