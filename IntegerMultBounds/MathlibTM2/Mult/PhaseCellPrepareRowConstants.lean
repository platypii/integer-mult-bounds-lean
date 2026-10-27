module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoefficientRow

/-! Prepare constants once while retaining the numeric row headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellRationalArgs

def prepareRowConstants : TblCode 50 := prepareDirectCoefficient.rename coefficientSweepReg

theorem prepareRowConstants_do {A w q P s t u band i : ℕ} (st : TblSt 50 A)
    (hP' : st.val 19 = P) (hq : st.val 44 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hi' : st.val 37 = i) (hb : st.val 49 = band) (hP : 13 ≤ P) (hi : i < s) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w prepareRowConstants st
      (fun st' => CoefficientRowReady P q s t u band i st' ∧ st'.val 44 = q ∧ st'.acc = st.acc)
      (154*P+4*q+413) := by
  let V := liftedCoefficientWidth P q w s t u band
  have hf := withinCoefficientWidth_fits false P q w s t u band i 0 hi (by omega)
  have hp := (prepareDirectCoefficient_do (A := A) (w := w) (V := V)
    (st.restrict coefficientSweepReg) hP' hq hP hf.semanticWidth (by have hh := hf.gridWidth; omega)).rename
      coefficientSweepReg_injective
  refine hp.mono (fun st₁ h₁ => ?_) le_rfl
  have hframe (r : Fin 48) (hr : 34 ≤ r.val) (h39 : r ≠ 39) (h40 : r ≠ 40) (h45 : r ≠ 45) :
      st₁.val (coefficientSweepReg r) = st.val (coefficientSweepReg r) := h₁.1.2.2.2.2.2.2 r hr h39 h40 h45
  have h49 : st₁.val 49 = st.val 49 := h₁.2 49 (fun k he => by
    have hk := k.isLt; have hv := congrArg Fin.val he; simp [coefficientSweepReg] at hv; omega)
  refine ⟨?_,?_,h₁.1.2.2.2.2.2.1⟩
  · constructor
    · simpa [coefficientSweepReg,TblSt.restrict] using h₁.1.1
    · simpa [coefficientSweepReg,TblSt.restrict] using h₁.1.2.1
    · simpa [coefficientSweepReg,TblSt.restrict] using h₁.1.2.2.1
    · exact (hframe 34 (by decide) (by decide) (by decide) (by decide)).trans hs
    · exact (hframe 35 (by decide) (by decide) (by decide) (by decide)).trans ht
    · exact (hframe 36 (by decide) (by decide) (by decide) (by decide)).trans hu
    · exact (hframe 37 (by decide) (by decide) (by decide) (by decide)).trans hi'
    · simpa [coefficientSweepReg,TblSt.restrict] using h₁.1.2.2.2.1
    · simpa [coefficientSweepReg,TblSt.restrict] using h₁.1.2.2.2.2.1
    · exact h49.trans hb
  · exact (hframe 44 (by decide) (by decide) (by decide) (by decide)).trans hq

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
