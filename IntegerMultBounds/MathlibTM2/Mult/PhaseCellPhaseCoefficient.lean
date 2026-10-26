module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhaseWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDirectCoefficient

/-! Select the actual off-diagonal coefficient branch by executed natural
phase comparisons. Both branches use the original ambient coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def phaseCoefficientBody : TblCode 48 := phaseArguments ;;
  tableIfEq 42 43 withinCoefficientBody directCoefficientBody

theorem phaseCoefficientBody_do {A w q P s t u band i d : ℕ}
    (negative : Bool) (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = liftedSource s band i) (hk : st.val 38 = liftedTarget negative s band i d)
    (hq : st.val 39 = 2^q) (hpowP : st.val 40 = 2^P)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band) (hi : i < s)
    (hjk : liftedSource s band i ≠ liftedTarget negative s band i d) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w phaseCoefficientBody st
      (fun st' => st'.acc = (csyms A w (rationalWord q
        (PhaseCellCrossCell.entry P s t u band (liftedSource s band i)
          (liftedTarget negative s band i d)))).reverse ++ st.acc) (930*P+365) := by
  let V := liftedCoefficientWidth P q w s t u band
  have hc := liftedCoefficientWidth_fits negative P q w s t u band i d hi hd
  have hw := withinCoefficientWidth_fits negative P q w s t u band i d hi hd
  have hp := phaseCoefficientWidth_fits negative P q w s t u band i d hs0 hi hd
  have hband : (((liftedTarget negative s band i d : ℕ) : ℤ)-
      (liftedSource s band i : ℕ)).natAbs ≤ band := by
    rw [← naturalDistance_eq_natAbs,lifted_naturalDistance negative hs0 hd]
    exact hd
  have hargs := phaseArguments_do (w := w) st hs ht hj hk hc.twiceModulus
    hc.sourceIndex hc.targetIndex hp.1 hp.2
  have hcore : TblDo A V w phaseCoefficientBody st
      (fun st' => st'.acc = (csyms A w (rationalWord q
        (PhaseCellCrossCell.entry P s t u band (liftedSource s band i)
          (liftedTarget negative s band i d)))).reverse ++ st.acc) (11+((930*P+352)+2)) := by
    unfold phaseCoefficientBody
    refine hargs.seq (fun s₁ h₁ => ?_)
    have hf (r : Fin 48) (hr : r ∉ [(41 : Fin 48),42,43]) := h₁.2.2.2 r hr
    apply tableIfEq_do
    · intro he
      rw [h₁.1,h₁.2.1] at he
      have hphase := (phaseArguments_eq_iff s t (liftedSource s band i)
        (liftedTarget negative s band i d)).mp he
      have hbody := withinCoefficientBody_do (w := w) (band := band) s₁
        ((hf 18 (by simp)).trans hpi)
        ((hf 19 (by simp)).trans hP')
        ((hf 22 (by simp)).trans hneg)
        ((hf 34 (by simp)).trans hs)
        ((hf 35 (by simp)).trans ht)
        ((hf 36 (by simp)).trans hu)
        ((hf 37 (by simp)).trans hj)
        ((hf 38 (by simp)).trans hk)
        ((hf 39 (by simp)).trans hq)
        ((hf 40 (by simp)).trans hpowP)
        hs0 hst hP hjk hband hw.sourceIndex hw.targetIndex hw.twiceModulus hw.targetDimension
        hw.modulusSquare hw.weightedSquare hw.denominator hw.semanticWidth hw.gridWidth
        hw.sourceExponent hw.targetExponent hw.distanceSquare hw.scaledDistance hw.weightedDistance
        hw.distanceExponent
      exact hbody.mono (fun s₂ h₂ => by
        simpa only [PhaseCellCrossCell.entry,if_pos hphase,h₁.2.2.1] using h₂.1) le_rfl
    · intro he
      have hphase : PhaseCellCrossCell.phaseQ s t (liftedSource s band i) ≠
          PhaseCellCrossCell.phaseQ s t (liftedTarget negative s band i d) := by
        intro hh
        apply he
        rw [h₁.1,h₁.2.1]
        exact (phaseArguments_eq_iff _ _ _ _).mpr hh
      have hbody := directCoefficientBody_do (w := w) s₁
        ((hf 18 (by simp)).trans hpi)
        ((hf 19 (by simp)).trans hP')
        ((hf 22 (by simp)).trans hneg)
        ((hf 34 (by simp)).trans hs)
        ((hf 35 (by simp)).trans ht)
        ((hf 36 (by simp)).trans hu)
        ((hf 37 (by simp)).trans hj)
        ((hf 38 (by simp)).trans hk)
        ((hf 39 (by simp)).trans hq)
        ((hf 40 (by simp)).trans hpowP)
        hs0 hst hP hc.sourceIndex hc.targetIndex hc.twiceModulus hc.sourceNearest hc.targetNearest
        hc.sourceSquare hc.targetSquare hc.modulusSquare hc.semanticWidth hc.exponentWidth hc.gridWidth
      exact hbody.mono (fun s₂ h₂ => by
        simpa only [PhaseCellCrossCell.entry,if_neg hphase,if_pos hband,h₁.2.2.1] using h₂.1) (by omega)
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
