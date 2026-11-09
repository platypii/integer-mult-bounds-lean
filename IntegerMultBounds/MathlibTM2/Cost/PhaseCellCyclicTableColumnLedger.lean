module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableColumn
import Mathlib.Tactic.Ring

/-! Complete column assembly: retain numerical/collection calls and replace
index, lookup and publication controls by one explicit scalar polynomial. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem cyclicTableColumnControls_poly {k j band V q Z : ℕ}
    (hZ : 1 ≤ Z) (hk : k ≤ Z) (hj : j ≤ Z) (hb : band ≤ Z)
    (hV : V ≤ Z) (hq : q ≤ Z) :
    10000*(k+j+band+V+1)*(q+V+1) ≤ 150000*Z^2 := by
  have hleft : k+j+band+V+1 ≤ 5*Z := by omega
  have hright : q+V+1 ≤ 3*Z := by omega
  have hprod := Nat.mul_le_mul hleft hright
  nlinarith only [hprod]

theorem cyclicTableColumnCost_le_components (p u l s t a n target k j : ℕ) [NeZero s] :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    let band := PhaseCellBand.width p u
    let V := publicationGeometryWidth t band
    let B := cyclicPrincipalBoundary s t band a n
    cyclicTableColumnCost p u l s t a n target k j ≤
      arbitraryOriginalColumnCost p q s t u j+
      windowedSchurResidualCost p l s t u target 2 a (a+min n (s-a))+
      windowedSchurResidualCost p l s t u target 2 0 (n-min n (s-a))+
      collectRetireCyclicColumnCost B q V band a (a+min n (s-a)) k+
      10000*(k+j+band+V+1)*(q+V+1) := by
  dsimp only
  have hlen := foldedBandRows_length_le
    (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n) (24*PhaseCellBand.width p u+1) k
  have hm := Nat.mul_le_mul_right
    (2*executionPrecision p l (initialSchurTarget p u target 2) 2+8) hlen
  unfold cyclicTableColumnCost retainedIndexedCyclicColumnCost
  dsimp only
  ring_nf at hm ⊢
  omega

end IntegerMultBounds.MathlibTM2.Cost
