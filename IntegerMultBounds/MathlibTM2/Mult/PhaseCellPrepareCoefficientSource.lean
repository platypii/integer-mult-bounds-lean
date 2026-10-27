module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoefficientSweep

/-! Compute the source similarity sample once before either offset sweep. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling.WeightNat IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def prepareCoefficientSource : TblCode 50 :=
  (withinSimilaritySetup ;; (similaritySampleAt false ;; .ins (.copy 41 26))).rename coefficientSweepReg

theorem prepareCoefficientSource_do {A w q P s t u band i : ℕ} (st : TblSt 50 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = liftedSource s band i)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hi : i < s) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w prepareCoefficientSource st
      (fun st' => st'.val 26 = similarityGridNumerator P s t u (liftedSource s band i) ∧
        st'.acc = st.acc ∧ ∀ r ∈ [(18 : Fin 50),19,22,34,35,36,37,38,39,40,48,49],
          st'.val r = st.val r) (310*P+121) := by
  let V := liftedCoefficientWidth P q w s t u band
  let initial := st.restrict coefficientSweepReg
  have hf := withinCoefficientWidth_fits false P q w s t u band i 0 hi (Nat.zero_le _)
  have hsetup := withinSimilaritySetup_do (A := A) (V := V) (w := w) initial hs ht hst
    hf.twiceModulus hf.targetDimension hf.denominator
  have hrun : TblDo A V w
      (withinSimilaritySetup ;; (similaritySampleAt false ;; .ins (.copy 41 26))) initial
      (fun st' => st'.val 26 = similarityGridNumerator P s t u (liftedSource s band i) ∧
        st'.acc = initial.acc) (5+((310*P+115)+1)) := by
    refine hsetup.seq (fun s₀ h₀ => ?_)
    have hoff (r : Fin 48) (h44 : r ≠ 44) (h47 : r ≠ 47) := h₀.2.2.2 r h44 h47
    have hsample := similaritySampleAt_do (A := A) (V := V) (w := w) false s₀
      ((hoff 18 (by decide) (by decide)).trans hpi)
      ((hoff 19 (by decide) (by decide)).trans hP')
      ((hoff 22 (by decide) (by decide)).trans hneg)
      ((hoff 34 (by decide) (by decide)).trans hs)
      ((hoff 35 (by decide) (by decide)).trans ht)
      ((hoff 36 (by decide) (by decide)).trans hu)
      ((hoff 37 (by decide) (by decide)).trans hj)
      h₀.1 h₀.2.1 hP hs0 hst hf.sourceIndex hf.twiceModulus hf.modulusSquare
      hf.weightedSquare hf.semanticWidth hf.sourceExponent
    refine hsample.seq (fun s₁ h₁ => ?_)
    have hsamp : s₁.val 41 = similarityGridNumerator P s t u (liftedSource s band i) := by simpa using h₁.1
    apply TblDo.insX (.copy 41 26) trivial
    simp [TblIns.exact,hsamp,h₁.2.1,h₀.2.2.1]
  have hr := (hrun.rename coefficientSweepReg_injective).keep
  refine hr.mono (fun st' h => ⟨h.1.1.1,h.1.1.2,?_⟩) (by omega)
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact h.2 _ (by decide)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
