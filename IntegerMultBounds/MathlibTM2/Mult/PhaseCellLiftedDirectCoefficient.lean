module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareDirectCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftCouplingCoordinates

/-! Generate constants, lift a signed offset and evaluate its direct coefficient.
The table input contains only dimensions, coordinates and precision values. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs

def liftedDirectCoefficientCode (negative : Bool) : TblCode 48 :=
  prepareDirectCoefficient ;; (liftCouplingCoordinates negative ;; directCoefficientBody)

theorem liftedDirectCoefficientCode_do {A V w q P s t u band i d : ℕ}
    (negative : Bool) (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hq : st.val 44 = q)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hi : st.val 37 = i) (hb : st.val 41 = band) (hd' : st.val 42 = d)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P) (hd : d ≤ band)
    (hfit : i+band*s+d < 2^V)
    (hjV : 2*t*liftedSource s band i+s < 2^V)
    (hkV : 2*t*liftedTarget negative s band i d+s < 2^V) (hsV : 2*s < 2^V)
    (hnjV : s*nearestNatural s t (liftedSource s band i) < 2^V)
    (hnkV : s*nearestNatural s t (liftedTarget negative s band i d) < 2^V)
    (hdjV : latticeDistance s t (liftedSource s band i) (liftedTarget negative s band i d)^2 < 2^V)
    (hdkV : latticeDistance s t (liftedTarget negative s band i d) (liftedTarget negative s band i d)^2 < 2^V)
    (hsqV : s^2 < 2^V) (hV : 13*P+8 ≤ V)
    (haV : latticeNumerator s t u (liftedSource s band i) (liftedTarget negative s band i d)*
      2^(5*P+2) < 2^V) (hqV : q+P+2 ≤ V) :
    TblDo A V w (liftedDirectCoefficientCode negative) st (fun st' => st'.acc =
      (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u
        (liftedSource s band i) (liftedTarget negative s band i d)))).reverse++st.acc)
      (464*P+4*q+545) := by
  have hsetup := prepareDirectCoefficient_do (w := w) st hP' hq hP hV hqV
  have hcore : TblDo A V w (liftedDirectCoefficientCode negative) st (fun st' => st'.acc =
      (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u
        (liftedSource s band i) (liftedTarget negative s band i d)))).reverse++st.acc)
      ((154*P+4*q+413)+(3+(310*P+129))) := by
    unfold liftedDirectCoefficientCode
    refine hsetup.seq (K₂ := 3+(310*P+129)) (fun s₁ h₁ => ?_)
    have hfr (r : Fin 48) (hr : 34 ≤ r.val) (hr39 : r ≠ 39) (hr40 : r ≠ 40) (hr45 : r ≠ 45) :=
      h₁.2.2.2.2.2.2 r hr hr39 hr40 hr45
    have hlift := liftCouplingCoordinates_do (A := A) (V := V) (w := w) negative s₁
      ((hfr 34 (by decide) (by decide) (by decide) (by decide)).trans hs)
      ((hfr 37 (by decide) (by decide) (by decide) (by decide)).trans hi)
      ((hfr 41 (by decide) (by decide) (by decide) (by decide)).trans hb)
      ((hfr 42 (by decide) (by decide) (by decide) (by decide)).trans hd') hs0 hd hfit
    refine hlift.seq (K₂ := 310*P+129) (fun s₂ h₂ => ?_)
    have hf (r : Fin 48) (hr : r ∉ [(37 : Fin 48),38,43]) := h₂.2.2.2 r hr
    have hc := directCoefficientBody_do (w := w) s₂
      ((hf 18 (by simp)).trans h₁.1) ((hf 19 (by simp)).trans h₁.2.1)
      ((hf 22 (by simp)).trans h₁.2.2.1)
      ((hf 34 (by simp)).trans ((hfr 34 (by decide) (by decide) (by decide) (by decide)).trans hs))
      ((hf 35 (by simp)).trans ((hfr 35 (by decide) (by decide) (by decide) (by decide)).trans ht))
      ((hf 36 (by simp)).trans ((hfr 36 (by decide) (by decide) (by decide) (by decide)).trans hu))
      h₂.1 h₂.2.1 ((hf 39 (by simp)).trans h₁.2.2.2.1) ((hf 40 (by simp)).trans h₁.2.2.2.2.1)
      hs0 hst hP hjV hkV hsV hnjV hnkV hdjV hdkV hsqV hV haV hqV
    exact hc.mono (fun s₃ h => by simpa only [h₂.2.2.1,h₁.2.2.2.2.2.1] using h.1) le_rfl
  exact hcore.mono (fun _ h => h) (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
