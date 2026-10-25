module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Fast.TableWeight
public import IntegerMultBounds.NLogN.PhaseCellCoefficientArgs

/-! Corrected exponential evaluation without emission, for reuse by both
similarity weight encoders. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

def correctExpValue : TblCode 34 :=
  tblBlock 34 (tblConstL 24 2) (.zero 25) ;;
    .ite 23 24 (.ins (.zero 23)) (.ins (.sub 23 24 23))

theorem correctExpValue_do {A V w E : ℕ} (st : TblSt 34 A)
    (hE : st.val 23 = E) (hEV : E < 2 ^ V) (hV : 2 ≤ V) :
    TblDo A V w correctExpValue st (fun s => s.val 23 = E - 2 ∧
      s.val 25 = 0 ∧ s.acc = st.acc ∧
      ∀ k, k ∉ [(23 : Fin 34), 24, 25] → s.val k = st.val k) 6 := by
  have htwo : 2 < 2 ^ V := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hV)
  let S₁ : TblSt 34 A := ⟨Function.update (Function.update st.val 24 2) 25 0, st.acc⟩
  have hprep : TblDo A V w (tblBlock 34 (tblConstL 24 2) (.zero 25)) st
      (fun s => s = S₁) 4 := by
    apply TblDo.block
    · apply tblFitsList_append _ _ _ (tblFitsList_const _ _ _ htwo)
      simp [tblFitsList, TblIns.fits]
    · simp [tblExactList_append, tblExactList_const, tblExactList, TblIns.exact, S₁]
  have hbranch : TblDo A V w
      (.ite 23 24 (.ins (.zero 23)) (.ins (.sub 23 24 23))) S₁
      (fun s => s.val 23 = E - 2 ∧ s.val 25 = 0 ∧ s.acc = st.acc) 2 := by
    by_cases hlt : E < 2
    · apply TblDo.iteT (by simpa [S₁, hE] using hlt)
      apply TblDo.insX (.zero 23) trivial
      simp [TblIns.exact, S₁, Nat.sub_eq_zero_of_le hlt.le]
    · apply TblDo.iteF (by simpa [S₁, hE] using hlt)
      apply TblDo.insX (.sub 23 24 23)
        (show (TblIns.sub 23 24 23).fits A V S₁ by simp [TblIns.fits, S₁, hE]; omega)
      simp [TblIns.exact, S₁, hE]
  have hcore : TblDo A V w correctExpValue st
      (fun s => s.val 23 = E - 2 ∧ s.val 25 = 0 ∧ s.acc = st.acc) 6 := by
    unfold correctExpValue
    exact hprep.seq (fun s hs => hs ▸ hbranch)
  exact hcore.keep.mono (fun s ⟨hs, hk⟩ => ⟨hs.1, hs.2.1, hs.2.2, fun k h => hk k (by
    simpa [correctExpValue, TblCode.tblDsts, tblBlock, tblStraight,
      tblConstL, TblIns.tblDst, and_comm, and_left_comm, and_assoc] using h)⟩) le_rfl

def correctedExpCode : TblCode 34 := tblExpCode ;; correctExpValue

/-- Evaluate once and retain the sampled numerator for both natural divisions. -/
theorem correctedExpCode_do {A V w P a b : ℕ} (st : TblSt 34 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (ha : st.val 20 = a)
    (hb' : st.val 21 = b) (hneg : st.val 22 = 1) (hP : 13 ≤ P) (hb : 0 < b)
    (hV : 13 * P + 8 ≤ V) (haV : a * 2 ^ (5 * P + 2) < 2 ^ V) :
    TblDo A V w correctedExpCode st (fun s =>
      s.val 23 = PhaseCellExpSample.numerator P a b ∧ s.val 25 = 0 ∧
      s.acc = st.acc ∧ s.val 18 = st.val 18 ∧ s.val 19 = st.val 19 ∧
      s.val 21 = st.val 21 ∧ s.val 22 = st.val 22) (310 * P + 106) := by
  have hraw := tblExp_do (A := A) (W := V) (w := w) st true
    hpi hP' ha hb' (by simpa using hneg) hP hV haV (by simp)
  have hE := expPiNat_neg_lt_pow hP (by omega : P + 2 ≤ V) a b hb
  refine (hraw.seq (fun s hs => (correctExpValue_do s hs.1 hE (by omega)).mono
    (fun s' ⟨hn, hz, hout, hkeep⟩ => ?_) le_rfl)).mono (fun _ h => h) (by omega)
  refine ⟨hn, hz, hout.trans hs.2.2.2.2.2.2, ?_, ?_, ?_, ?_⟩
  · exact (hkeep 18 (by simp)).trans hs.2.1
  · exact (hkeep 19 (by simp)).trans hs.2.2.1
  · exact (hkeep 21 (by simp)).trans hs.2.2.2.2.1
  · exact (hkeep 22 (by simp)).trans hs.2.2.2.2.2.1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
