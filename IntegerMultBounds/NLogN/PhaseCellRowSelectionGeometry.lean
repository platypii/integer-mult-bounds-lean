module

public import IntegerMultBounds.NLogN.PhaseCellLatticeArgs

/-! A near-one row selector expands a source guard by at most twice its radius
plus one rounding unit. Containment uses original global row indices. -/
@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem nearestNatural_add_le (s t i r : ℕ) (hs : 0 < s) (ht : t ≤ 2*s) :
    nearestNatural s t (i+r) ≤ nearestNatural s t i+2*r+1 := by
  have hden : 0 < 2*s := by omega
  have hupper := Nat.mul_div_le (2*t*(i+r)+s) (2*s)
  have hlower := Nat.lt_mul_div_succ (2*t*i+s) hden
  have hstep := Nat.mul_le_mul_right (2*r) ht
  apply Nat.le_of_mul_le_mul_left (c := 2*s) ?_ hden
  dsimp only [nearestNatural]
  nlinarith only [hupper,hlower,hstep]

/-- The nearest rows of a guarded source core fit the stored target halo.
Wrapping cores are split into such original-coordinate intervals separately. -/
theorem nearestNatural_halo_contained (s t a n radius base L H : ℕ)
    (hs : 0 < s) (ht : t ≤ 2*s) (hn : 0 < n) (ha : radius ≤ a) (hb : H ≤ base)
    (hguard : 2*radius+1 ≤ H)
    (hfirst : base ≤ nearestNatural s t a)
    (hlast : nearestNatural s t (a+n-1) < base+L) :
    ∀ j < n+2*radius, base-H ≤ nearestNatural s t (a-radius+j) ∧
      nearestNatural s t (a-radius+j) < base-H+(L+2*H) := by
  intro j hj
  let q := a-radius+j
  have hmono : Monotone (nearestNatural s t) := by
    intro x y hxy
    exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_left (2*t) hxy) s)
  have hlow : base ≤ nearestNatural s t q+H := by
    by_cases hqa : q ≤ a
    · have hh := nearestNatural_add_le s t q (a-q) hs ht
      rw [Nat.add_sub_of_le hqa] at hh
      have hr : a-q ≤ radius := by dsimp only [q]; omega
      omega
    · have hh := hmono (show a ≤ q by omega)
      omega
  have hhigh : nearestNatural s t q < base+L+H := by
    by_cases haq : a+n-1 ≤ q
    · have hh := nearestNatural_add_le s t (a+n-1) (q-(a+n-1)) hs ht
      rw [Nat.add_sub_of_le haq] at hh
      have hr : q-(a+n-1) ≤ radius := by dsimp only [q]; omega
      omega
    · have hh := hmono (show q ≤ a+n-1 by omega)
      omega
  dsimp only [q] at hlow hhigh
  constructor <;> omega

end IntegerMultBounds.NLogN.PhaseCellRationalArgs
