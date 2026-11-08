module

public import IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
public import IntegerMultBounds.NLogN.PhaseCellRowSelectionGeometry

/-! Relate the manuscript's floor-defined source ownership to the global
nearest-row selector. Rounding needs two rows of lower-end slack. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
open PhaseCellRationalArgs

theorem nearest_lower_of_cut (s t b j : ℕ) (hs : 0 < s) (ht : 0 < t) (hnear : t ≤ 2*s)
    (hj : b*s/t ≤ j) : b ≤ nearestNatural s t j+2 := by
  have hcut := Nat.lt_mul_div_succ (b*s) ht
  have hjmul := Nat.mul_le_mul_left t hj
  have hround := Nat.lt_mul_div_succ (2*t*j+s) (show 0 < 2*s by omega)
  by_contra hbad
  have hh := Nat.mul_le_mul_left s (show nearestNatural s t j+3 ≤ b by omega)
  dsimp only [nearestNatural] at hh
  nlinarith only [hcut,hjmul,hround,hh,hnear]

theorem nearest_upper_of_cut (s t b j : ℕ) (hs : 0 < s) (hst : s ≤ t)
    (hj : j < b*s/t) : nearestNatural s t j < b := by
  have hcut := Nat.mul_div_le (b*s) t
  have hjmul := Nat.mul_le_mul_left t (show j+1 ≤ b*s/t by omega)
  have hround := Nat.mul_div_le (2*t*j+s) (2*s)
  by_contra hbad
  have hh := Nat.mul_le_mul_left (2*s) (show b ≤ nearestNatural s t j by omega)
  dsimp only [nearestNatural] at hh
  nlinarith only [hcut,hjmul,hround,hh,hst,hs]

theorem selected_owned_rows (s t L k j : ℕ) (hs : 0 < s) (hst : s ≤ t)
    (ht : 0 < t) (hnear : t ≤ 2*s)
    (hj : cut s t L k ≤ j ∧ j < cut s t L (k+1)) :
    k*L ≤ nearestNatural s t j+2 ∧ nearestNatural s t j < (k+1)*L := by
  constructor
  · exact nearest_lower_of_cut s t (k*L) j hs ht hnear hj.1
  · exact nearest_upper_of_cut s t ((k+1)*L) j hs hst hj.2

/-- The all-row containment premise for the actual floor-owned source core
and its locality guard, in original nonwrapping ambient coordinates. -/
theorem owned_halo_contained (s t L k radius H : ℕ)
    (hs : 0 < s) (hst : s ≤ t) (ht : 0 < t) (hnear : t ≤ 2*s)
    (hn : 0 < rows s t L k) (ha : radius ≤ cut s t L k) (hb : H ≤ k*L)
    (hguard : 2*radius+3 ≤ H) :
    ∀ j < rows s t L k+2*radius,
      k*L-H ≤ nearestNatural s t (cut s t L k-radius+j) ∧
        nearestNatural s t (cut s t L k-radius+j) < k*L-H+(L+2*H) := by
  have hmono := cut_mono s t L (show k ≤ k+1 by omega)
  have hnonempty : cut s t L k < cut s t L (k+1) := by dsimp only [rows] at hn; omega
  have hfirst := (selected_owned_rows s t L k (cut s t L k) hs hst ht hnear ⟨le_rfl,hnonempty⟩).1
  have hlast : nearestNatural s t (cut s t L k+rows s t L k-1) < k*L+L := by
    have hj : cut s t L k+rows s t L k-1 < cut s t L (k+1) := by
      dsimp only [rows]; omega
    have hh := nearest_upper_of_cut s t ((k+1)*L) _ hs hst hj
    simpa only [Nat.add_mul,Nat.one_mul] using hh
  exact nearestNatural_halo_contained s t (cut s t L k) (rows s t L k) radius (k*L) L H
    hs hnear hn ha hb hguard hfirst hlast

end IntegerMultBounds.NLogN.PhaseCellTargetCoreOwnership
