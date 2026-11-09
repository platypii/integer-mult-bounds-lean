module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedCyclicFactor
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellScaledFactorPagePolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellScaledFactorSetupPolynomial

/-! The complete cyclic factory adds polynomial page and factor preparation
to its actual table scan. Numerical precision uses the joint boundary count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem constructedCyclicFactorCost_le_envelope
    (p u l s t a n target rhsExp R : ℕ) [NeZero s] :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let bits := boundaryTableBits p target rhsExp B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    1 ≤ R → q ≤ R → band ≤ R → 24*band+1 ≤ R → B.card ≤ R →
    2*q+8 ≤ R → B.card+2*(24*band+1)+2 ≤ R →
    p+2*q+24*band+B.card+100 ≤ R →
    constructedCyclicFactorCost p u l s t a n target rhsExp ≤
      cyclicTableColumnsLoopCost p u l s t a n bits+8*B.card+9+
        10000020*R^5+(1000000+10000000*(ssMulConst+1))*R^6 := by
  dsimp only
  intro hR hq hb hW hN hw henv hsetup
  have hpage := scaledGeneratedFactorPageCost_poly hR hq hb hW hN hw henv
  have hprep := scaledFactorPreparationCost_poly p
    (executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target rhsExp
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2)
    (PhaseCellBand.width p u) (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
  have hs := Nat.mul_le_mul_left (1000000+10000000*(ssMulConst+1))
    (Nat.pow_le_pow_left hsetup 6)
  have heq (p l z : ℕ) : executionWidth p l z 2 = 2*executionPrecision p l z 2+8 := by
    unfold executionWidth executionPrecision
    omega
  unfold constructedCyclicFactorCost
  dsimp only
  rw [heq]
  omega

end IntegerMultBounds.MathlibTM2.Cost
