module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArbitraryOriginalColumn
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUncachedCouplingPolynomial
import Mathlib.Tactic.Ring

/-! Separate the actual arbitrary-column coupling from its scalar headers and
linear zero-source initialization, copying and retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem arbitraryOriginalColumnCost_split (p q s t u j : ℕ) :
    arbitraryOriginalColumnCost p q s t u j =
      borrowedCouplingPassCost true (2^15*p) q (2*q+8) s t u
        (PhaseCellBand.width p u) j (j+1)+
      installCouplingHeadersCost (2^15*p) q s t u (PhaseCellBand.width p u) j (j+1)+
      releaseCouplingHeadersCost (2^15*p) q s t u (PhaseCellBand.width p u) j (j+1)+
      50*s*(2*q+8)+44*s+2*q+18*j+102 := by
  unfold arbitraryOriginalColumnCost restoredOriginalColumnCost generatedOriginalColumnCost
    originalColumnInputsCost releaseColumnSourcesCost
  ring

/-- All source/header work is uniform over the physical column index.
Only the one-point coupling retains that index for the numerical estimate. -/
theorem arbitraryOriginalColumnCost_controls_le (p q s t u j : ℕ) (hj : j < s) :
    arbitraryOriginalColumnCost p q s t u j ≤
      borrowedCouplingPassCost true (2^15*p) q (2*q+8) s t u
        (PhaseCellBand.width p u) j (j+1)+
      50*s*(2*q+8)+80*s+20*q+6*(2^15*p)+6*t+6*u+
        6*PhaseCellBand.width p u+185 := by
  rw [arbitraryOriginalColumnCost_split]
  unfold installCouplingHeadersCost releaseCouplingHeadersCost
  ring_nf
  omega

/-- Use the endpoint-uniform uncached numerical polynomial. Mask generation
remains explicit, so no interval-dependent setup is silently discarded. -/
theorem arbitraryOriginalColumnCost_numerical_poly (p q s t u j R : ℕ)
    (hj : j < s) (hR : 1 ≤ R) (ht : 1 ≤ t) (hst : s ≤ t) (htR : t ≤ R)
    (hP : 2^15*p ≤ R) (hq : q ≤ R) (hw : 2*q+8 ≤ R)
    (hu : u ≤ R) (hband : PhaseCellBand.width p u ≤ R)
    (hV : liftedCoefficientWidth (2^15*p) q (2*q+8) s t u (PhaseCellBand.width p u) ≤ R) :
    arbitraryOriginalColumnCost p q s t u j ≤
      closedCouplingSourceMaskCost s t (PhaseCellBand.width p u) j (j+1)+
      prepareCouplingGuardCost s t (PhaseCellBand.width p u) j (j+1)+
      10000000*(ssMulConst+1)*R^5+
      50*s*(2*q+8)+80*s+20*q+6*(2^15*p)+6*t+6*u+
        6*PhaseCellBand.width p u+185 := by
  have hc := borrowedCouplingPassCost_poly (a := j) (b := j+1)
    hR ht hst htR hP hq hw (by omega) hu hband hV true
  have h := arbitraryOriginalColumnCost_controls_le p q s t u j hj
  have ha := Nat.add_le_add_right hc
    (50*s*(2*q+8)+80*s+20*q+6*(2^15*p)+6*t+6*u+6*PhaseCellBand.width p u+185)
  simp only [Nat.add_assoc] at h ha ⊢
  exact h.trans ha

end IntegerMultBounds.MathlibTM2.Cost
