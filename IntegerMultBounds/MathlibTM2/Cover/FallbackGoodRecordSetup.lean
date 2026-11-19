module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordCost
import IntegerMultBounds.MathlibTM2.Cover.FallbackPrefixVolume

/-! Bounds for good-record setup before any payload symbols are charged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback

/-- Pivot preparation and child-weight encoding cost at most a quadratic in
the modulus bit width per precision digit, uniformly over the pivot archive. -/
theorem goodPivotSetup_le (b d w H a gap : ℕ) (ha : a ≤ d) (hg : gap ≤ d) :
    headPivotPrepareTime b d w H a gap + tailPivotTime b w H a + childWeightTime b w H a ≤
      2000*(b+1)*(d+1)^3*(w+1)*(H+1)^2 := by
  simp only [headPivotPrepareTime,tailPivotTime,childWeightTime]
  grw [Nat.sub_le b 2, Nat.div_le_self gap 2, hg, ha]
  ring_nf
  omega

/-- The head pass includes the tail address in its width header. At zero
payload its setup still loses one full modulus factor against total volume. -/
theorem goodHeadShearSetup_le {d : ℕ} (k t : Fin d) (M H : ℕ) (positive : 0 < M) :
    weightedShearTime k t M 0 H (d*H) ≤ M^(d+d-1)*(7100*(d+1)^2*(H+1)^2) := by
  rw [weightedShearTime_eq_setup_add_width_volume k t M 0 H (d*H)]
  have scale : M^(d-1) ≤ M^(d+d-1) := Nat.pow_le_pow_right positive (by omega)
  have one : 1 ≤ M^(d+d-1) := pow_pos positive _
  grw [weightedShearTime_setup_le_width k t M H positive,scale,show d-1-t.val ≤ d by omega]
  simp only [Nat.mul_zero,Nat.add_zero]
  generalize M^(d+d-1) = count at one ⊢
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le one
  ring_nf
  omega

/-- Preparing all child weights, constructing the middle field, calling the
child and clearing its headers add a polynomial toll to the child's own time. -/
theorem goodChildOverhead_le (b w H r g budget : ℕ) :
    (((List.finRange r).map fun i => childWeightTime b w H i.val).sum+1 + dimensionTime H 1 (g+g)) +
        (budget+2+(2*(r*H+r*H+((g+g)*H+1))+7)) ≤
      budget + 2200*(b+1)*(r+g+1)^4*(w+1)*(H+1)^2 := by
  let bound := 2000*(b+1)*(r+1)^3*(w+1)*(H+1)^2
  have each (i : Fin r) : childWeightTime b w H i.val ≤ bound :=
    (Nat.le_add_left ..).trans (goodPivotSetup_le b r w H i.val 0 i.isLt.le (Nat.zero_le _))
  have total (xs : List (Fin r)) :
      (xs.map fun i => childWeightTime b w H i.val).sum ≤ xs.length*bound := by
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simpa only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm] using
        Nat.add_le_add (each i) ih
  have weights := total (List.finRange r)
  simp only [List.length_finRange,bound] at weights
  grw [weights,dimensionTime_le H 1 (g+g)]
  generalize hd : r+g = d
  have hr : r ≤ d := by omega
  have hg : g ≤ d := by omega
  calc
    _ ≤ d*(2000*(b+1)*(d+1)^3*(w+1)*(H+1)^2)+1 + (6*1+6+(d+d)*((12*H+18)*((d+d)*H+1)+20*H+26)) + (budget+2+(2*(d*H+d*H+((d+d)*H+1))+7)) := by gcongr
    _ ≤ _ := by
      ring_nf
      omega

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
theorem goodChildOverhead_volume_le (r g : ℕ) (dim : 0 < r+g) :
    ∃ C : ℕ, ∀ w W budget, 0 < W →
      let q := prime^(w+1)
      let H := Nat.size q
      (((List.finRange r).map fun i => childWeightTime prime w H i.val).sum+1 + dimensionTime H 1 (g+g)) +
        (budget+2+(2*(r*H+r*H+((g+g)*H+1))+7)) ≤ budget + C*(q^((r+g)+(r+g))*W) := by
  let c := 2200*(prime+1)*(r+g+1)^4
  refine ⟨c*(2*(Nat.size prime+1)^2),fun w W budget width => ?_⟩
  intro q H
  apply (goodChildOverhead_le prime w H r g budget).trans
  apply Nat.add_le_add_left
  have field := prefixSetup_volume_le w 0
  change (w+1+q^0)*(H+1)^2 ≤ _*q^(0+1) at field
  simp only [pow_zero,Nat.zero_add,pow_one] at field
  have bits := (Nat.mul_le_mul_right ((H+1)^2) (Nat.le_succ (w+1))).trans field
  have vol : q ≤ q^((r+g)+(r+g))*W := by
    calc
      q = q^1 := (pow_one _).symm
      _ ≤ q^((r+g)+(r+g)) := Nat.pow_le_pow_right (by exact pow_pos (IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos) _) (by omega)
      _ ≤ _ := Nat.le_mul_of_pos_right _ width
  change c*(w+1)*(H+1)^2 ≤ _
  rw [Nat.mul_assoc c]
  grw [bits,vol]
  exact le_of_eq (by ring)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
