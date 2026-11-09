module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFactorPagePolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorPageSetup

/-! The cyclic factory's scale-24 page reuses the arbitrary-bandwidth page
polynomial. Scalar setup and retirement are charged once around that page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem scaledGeneratedFactorPageCost_poly {q band N R : ℕ}
    (hR : 1 ≤ R) (hq : q ≤ R) (hband : band ≤ R)
    (hW : 24*band+1 ≤ R) (hN : N ≤ R)
    (hw : 2*q+8 ≤ R) (henv : N+2*(24*band+1)+2 ≤ R) :
    scaledGeneratedFactorPageCost 24 q band N ≤ 10000020*R^5 := by
  have hp := factorPageCost_poly hR hq hW hN hw henv
  have hpow : R ≤ R^5 := Nat.le_self_pow (by decide) R
  unfold scaledGeneratedFactorPageCost
  omega

end IntegerMultBounds.MathlibTM2.Cost
