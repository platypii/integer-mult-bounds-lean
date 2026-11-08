module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.MathlibTM2.Routing.RectangularHaloCoordinates

/-! Cyclic storage is an ordered list of original ambient coordinates, not a
new periodic matrix. It agrees with packed intervals away from the seam. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Routing.RectangularHaloCoordinates

def cyclicInterval {s : ℕ} {E : Type} (a n : ℕ) (F : ZMod s → E) : List E :=
  (List.range n).map fun j => F ((a+j : ℕ) : ZMod s)

@[simp] theorem cyclicInterval_length {s : ℕ} {E : Type} (a n : ℕ) (F : ZMod s → E) :
    (cyclicInterval a n F).length = n := by simp [cyclicInterval]

theorem cyclicInterval_get {s a n j : ℕ} {E : Type} (F : ZMod s → E) (hj : j < n) :
    (cyclicInterval a n F)[j]'(by simpa using hj) = F ((a+j : ℕ) : ZMod s) := by
  simp [cyclicInterval]

theorem cyclicInterval_eq_packed {s a n : ℕ} (F : ZMod s → GaussianInt) (hfit : a+n ≤ s) :
    cyclicInterval a n F = packedInterval a n F := by
  apply List.ext_getElem (by rw [cyclicInterval_length,packedInterval_length F hfit])
  intro j hj hj'
  have hjn : j < n := by simpa using hj
  rw [cyclicInterval_get F hjn,packedInterval_get F hfit hjn]

theorem cyclicInterval_append {s : ℕ} {E : Type} (a m n : ℕ) (F : ZMod s → E) :
    cyclicInterval a (m+n) F = cyclicInterval a m F++cyclicInterval (a+m) n F := by
  simp [cyclicInterval,List.range_add,List.map_map,Function.comp_def,Nat.add_assoc]

theorem cyclicInterval_reduce {s : ℕ} {E : Type} (a n : ℕ) (F : ZMod s → E) :
    cyclicInterval (a%s) n F = cyclicInterval a n F := by
  simp [cyclicInterval,Nat.cast_add,ZMod.natCast_mod]

/-- A window of at most one period splits at the original physical seam.
The two pieces retain their original ambient interval coordinates. -/
theorem cyclicInterval_split {s a n : ℕ} (F : ZMod s → GaussianInt)
    (ha : a < s) (hn : n ≤ s) :
    cyclicInterval a n F = packedInterval a (min n (s-a)) F++
      packedInterval 0 (n-min n (s-a)) F := by
  by_cases hfit : a+n ≤ s
  · have hm : min n (s-a) = n := min_eq_left (by omega)
    rw [hm,cyclicInterval_eq_packed F hfit]
    simp [packedInterval]
  · have hm : min n (s-a) = s-a := min_eq_right (by omega)
    have hcount : (s-a)+(n-(s-a)) = n := by omega
    rw [hm,←hcount,cyclicInterval_append]
    have he : a+(s-a) = s := Nat.add_sub_of_le ha.le
    rw [he,cyclicInterval_eq_packed F (show a+(s-a) ≤ s by omega)]
    have hperiod : cyclicInterval s (n-(s-a)) F = cyclicInterval 0 (n-(s-a)) F := by
      simpa only [Nat.mod_self] using (cyclicInterval_reduce s (n-(s-a)) F).symm
    rw [hperiod,cyclicInterval_eq_packed F (show 0+(n-(s-a)) ≤ s by omega)]
    congr 2; omega

/-- This is exactly the periodic window retained by the executed halo pass. -/
theorem cyclicInterval_halo (N L H k : ℕ) (F : ZMod (N*L) → GaussianInt) (hH : H ≤ N*L) :
    cyclicInterval (N*L+k*L-H) (L+2*H) F =
      (List.range (L+2*H)).map (fun j => F (sourceIndex N L H k j)) := by
  apply List.map_congr_left
  intro j hj
  have he : N*L+k*L-H+j = N*L+(k*L+j)-H := by omega
  rw [he]
  simp only [sourceIndex,ZMod.natCast_mod]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
