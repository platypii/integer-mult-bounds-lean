module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Fast.TableWeight
public import IntegerMultBounds.NLogN.PhaseCellCoefficientArgs

/-! # Execute the corrected negative exponential used by phase-cell coefficients

The natural correction clamps at zero. The modular table subtraction therefore
runs only in the branch where the uncorrected sample is at least two.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

def correctExpEmit : TblCode 34 :=
  tblBlock 34 (tblConstL 24 2) (.zero 25) ;;
    .ite 23 24 (.ins (.zero 23)) (.ins (.sub 23 24 23)) ;;
      .ins (.emit 23 25)

/-- Correct and emit one nonnegative raw sample, preserving all other variables
except the explicitly private correction registers. -/
theorem correctExpEmit_do {A V w E : ℕ} (st : TblSt 34 A)
    (hE : st.val 23 = E) (hEV : E < 2 ^ V) (hV : 2 ≤ V) :
    TblDo A V w correctExpEmit st (fun s => s.val 23 = E - 2 ∧
      s.acc = (csyms A w (⟨((E - 2 : ℕ) : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc ∧
      ∀ k, k ∉ [(23 : Fin 34), 24, 25] → s.val k = st.val k) 7 := by
  have htwo : 2 < 2 ^ V := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hV)
  let S₁ : TblSt 34 A := ⟨Function.update (Function.update st.val 24 2) 25 0, st.acc⟩
  have hprep : TblDo A V w (tblBlock 34 (tblConstL 24 2) (.zero 25)) st (fun s => s = S₁) 4 := by
    apply TblDo.block
    · apply tblFitsList_append _ _ _ (tblFitsList_const _ _ _ htwo)
      simp [tblFitsList, TblIns.fits]
    · simp [tblExactList_append, tblExactList_const, tblExactList, TblIns.exact, S₁]
  let S₂ : TblSt 34 A := ⟨Function.update S₁.val 23 (E - 2), S₁.acc⟩
  have hbranch : TblDo A V w (.ite 23 24 (.ins (.zero 23)) (.ins (.sub 23 24 23)))
      S₁ (fun s => s = S₂) 2 := by
    by_cases hlt : E < 2
    · apply TblDo.iteT (by simpa [S₁, hE] using hlt)
      apply TblDo.insX (.zero 23) trivial
      simp [S₂, S₁, TblIns.exact, Nat.sub_eq_zero_of_le hlt.le]
    · apply TblDo.iteF (by simpa [S₁, hE] using hlt)
      apply TblDo.insX _
        (show (TblIns.sub 23 24 23).fits A V S₁ by simp [TblIns.fits, S₁, hE]; omega)
      simp [S₂, S₁, TblIns.exact, hE]
  have hemit : TblDo A V w (.ins (.emit 23 25)) S₂
      (fun s => s.val 23 = E - 2 ∧
        s.acc = (csyms A w (⟨((E - 2 : ℕ) : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc) 1 := by
    apply TblDo.insX (.emit 23 25) trivial
    simp [TblIns.exact, S₂, S₁, tbl_pairs_red, csyms]
  have hcore : TblDo A V w correctExpEmit st (fun s => s.val 23 = E - 2 ∧
      s.acc = (csyms A w (⟨((E - 2 : ℕ) : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc) 7 := by
    exact hprep.seq (fun s hs => hs ▸ hbranch.seq (fun s hs => hs ▸ hemit))
  exact hcore.keep.mono (fun s ⟨hs, hk⟩ => ⟨hs.1, hs.2, fun k h => hk k (by
    simpa [correctExpEmit, TblCode.tblDsts, tblBlock, tblStraight, tblConstL, TblIns.tblDst, and_comm, and_left_comm, and_assoc] using h)⟩) le_rfl

def coefficientExpCode : TblCode 34 := tblExpCode ;; correctExpEmit

/-- The corrected routine is precisely the natural coefficient constructor,
with the table machine's original pi and precision retained for reuse. -/
theorem coefficientExpCode_do {A V w P a b : ℕ} (st : TblSt 34 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (ha : st.val 20 = a)
    (hb' : st.val 21 = b) (hneg : st.val 22 = 1) (hP : 13 ≤ P) (hb : 0 < b)
    (hV : 13 * P + 8 ≤ V) (haV : a * 2 ^ (5 * P + 2) < 2 ^ V) :
    TblDo A V w coefficientExpCode st (fun s =>
      s.acc = (csyms A w (⟨(PhaseCellExpSample.numerator P a b : ℤ), 0⟩ : GaussianInt)).reverse ++ st.acc ∧
      s.val 18 = st.val 18 ∧ s.val 19 = st.val 19 ∧
      s.val 21 = st.val 21 ∧ s.val 22 = st.val 22) (310 * P + 107) := by
  have hraw := tblExp_do (A := A) (W := V) (w := w) st true hpi hP' ha hb' (by simpa using hneg) hP hV haV (by simp)
  have hE := expPiNat_neg_lt_pow hP (by omega : P + 2 ≤ V) a b hb
  refine (hraw.seq (fun s hs => (correctExpEmit_do s hs.1 hE (by omega)).mono
    (fun s' ⟨_, hout, hkeep⟩ => ?_) le_rfl)).mono (fun _ h => h) (by omega)
  refine ⟨by simpa only [PhaseCellExpSample.numerator, hs.2.2.2.2.2.2] using hout, ?_, ?_, ?_, ?_⟩
  · exact (hkeep 18 (by simp)).trans hs.2.1
  · exact (hkeep 19 (by simp)).trans hs.2.2.1
  · exact (hkeep 21 (by simp)).trans hs.2.2.2.2.1
  · exact (hkeep 22 (by simp)).trans hs.2.2.2.2.2.1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
