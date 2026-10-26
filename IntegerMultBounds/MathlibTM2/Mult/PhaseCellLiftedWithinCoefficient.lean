module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareDirectCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftCouplingCoordinates
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficientWidth

/-! Generate constants, lift a signed offset and evaluate its within-cell coefficient.
The table input contains only dimensions, coordinates and precision values. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def liftedWithinCoefficientCode (negative : Bool) : TblCode 48 :=
  prepareDirectCoefficient ;; (liftCouplingCoordinates negative ;; withinCoefficientBody)

theorem liftedWithinCoefficientCode_do {A w q P s t u band i d : ℕ}
    (negative : Bool) (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hq : st.val 44 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hi : st.val 37 = i) (hb : st.val 41 = band) (hd' : st.val 42 = d)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band)
    (hd0 : 0 < d) (hi0 : i < s) :
    TblDo A (liftedCoefficientWidth P q w s t u band) w (liftedWithinCoefficientCode negative) st (fun st' => st'.acc =
      (csyms A w (rationalWord q (PhaseCellConcreteCoefficients.entry P s t u band
        (liftedSource s band i) (liftedTarget negative s band i d)))).reverse++st.acc)
      (1084*P+4*q+768) := by
  let V := liftedCoefficientWidth P q w s t u band
  have hfits := withinCoefficientWidth_fits negative P q w s t u band i d hi0 hd
  have hfit := liftedCoefficientWidth_fits negative P q w s t u band i d hi0 hd
  have hdist := lifted_naturalDistance negative (s := s) (i := i) hs0 hd
  have hjk : liftedSource s band i ≠ liftedTarget negative s band i d := by
    intro he
    rw [he] at hdist
    simp [naturalDistance] at hdist
    omega
  have hband : (((liftedTarget negative s band i d : ℕ) : ℤ)-
      (liftedSource s band i : ℕ)).natAbs ≤ band := by
    rw [← naturalDistance_eq_natAbs,hdist]
    exact hd
  have hsetup := prepareDirectCoefficient_do (w := w) st hP' hq hP hfits.semanticWidth (by have hh := hfits.gridWidth; omega)
  have hcore : TblDo A (liftedCoefficientWidth P q w s t u band) w (liftedWithinCoefficientCode negative) st (fun st' => st'.acc =
      (csyms A w (rationalWord q (PhaseCellConcreteCoefficients.entry P s t u band
        (liftedSource s band i) (liftedTarget negative s band i d)))).reverse++st.acc)
      ((154*P+4*q+413)+(3+(930*P+352))) := by
    unfold liftedWithinCoefficientCode
    refine hsetup.seq (K₂ := 3+(930*P+352)) (fun s₁ h₁ => ?_)
    have hfr (r : Fin 48) (hr : 34 ≤ r.val) (hr39 : r ≠ 39) (hr40 : r ≠ 40) (hr45 : r ≠ 45) :=
      h₁.2.2.2.2.2.2 r hr hr39 hr40 hr45
    have hlift := liftCouplingCoordinates_do (A := A) (V := V) (w := w) negative s₁
      ((hfr 34 (by decide) (by decide) (by decide) (by decide)).trans hs)
      ((hfr 37 (by decide) (by decide) (by decide) (by decide)).trans hi)
      ((hfr 41 (by decide) (by decide) (by decide) (by decide)).trans hb)
      ((hfr 42 (by decide) (by decide) (by decide) (by decide)).trans hd') hs0 hd hfit.coordinates
    refine hlift.seq (K₂ := 930*P+352) (fun s₂ h₂ => ?_)
    have hf (r : Fin 48) (hr : r ∉ [(37 : Fin 48),38,43]) := h₂.2.2.2 r hr
    have hc := withinCoefficientBody_do (w := w) s₂
      ((hf 18 (by simp)).trans h₁.1) ((hf 19 (by simp)).trans h₁.2.1)
      ((hf 22 (by simp)).trans h₁.2.2.1)
      ((hf 34 (by simp)).trans ((hfr 34 (by decide) (by decide) (by decide) (by decide)).trans hs))
      ((hf 35 (by simp)).trans ((hfr 35 (by decide) (by decide) (by decide) (by decide)).trans ht))
      ((hf 36 (by simp)).trans ((hfr 36 (by decide) (by decide) (by decide) (by decide)).trans hu))
      h₂.1 h₂.2.1 ((hf 39 (by simp)).trans h₁.2.2.2.1) ((hf 40 (by simp)).trans h₁.2.2.2.2.1)
      hs0 hst hP hjk hband hfits.sourceIndex hfits.targetIndex hfits.twiceModulus
      hfits.targetDimension hfits.modulusSquare hfits.weightedSquare hfits.denominator
      hfits.semanticWidth hfits.gridWidth hfits.sourceExponent hfits.targetExponent
      hfits.distanceSquare hfits.scaledDistance hfits.weightedDistance hfits.distanceExponent
    exact hc.mono (fun s₃ h => by simpa only [h₂.2.2.1,h₁.2.2.2.2.2.1] using h.1) le_rfl
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
