module

public import IntegerMultBounds.MathlibTM2.Routing.HaloAxisSchedule
public import IntegerMultBounds.MathlibTM2.Routing.RetainedHaloVolume

/-! Exact mixed-layout volume factorizations. Padding only the selected field
costs less than twice the real tensor volume; count products omit that field. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMixedVolume
open RetainedHaloTensor RetainedTensorEnumeration HaloMixedOrder HaloMixedOrderRun HaloAxisSchedule
variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem movement_factorization (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) :
    ((moveBefore left i right).map (width axis retained)).prod*
      ((moveMiddle right).map (width axis retained)).prod*localLength axis retained i = volume axis retained := by
  have hv := enumerate_length_eq_volume axis retained (left++i::right) hn hall
  rw [enumerate_length] at hv
  rw [←hv]
  simp only [moveBefore,moveMiddle,List.map_append,List.map_cons,List.map_map,List.prod_append,List.prod_cons,
    Function.comp_def,width]
  ring

theorem halo_factorization (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) :
    ((haloBefore left).map (width axis retained)).prod*(axis i).N*
      ((haloMiddle left right).map (width axis retained)).prod*localLength axis retained i = volume axis retained := by
  have hv := enumerate_length_eq_volume axis retained (left++i::right) hn hall
  rw [enumerate_length] at hv
  rw [←hv]
  simp only [haloBefore,haloMiddle,List.map_append,List.map_cons,List.map_map,List.prod_append,List.prod_cons,
    Function.comp_def,width]
  ring

theorem padded_volume_le (a M k w T : ℕ) (hM : 0 < M) (he : a*M = T) (hpad : 2^k ≤ 2*M) :
    a*(2^k*w) ≤ 2*T*w := by
  apply Nat.le_of_mul_le_mul_right (c := M) ?_ hM
  calc
    a*(2^k*w)*M = T*(2^k*w) := by rw [←he]; ring
    _ ≤ T*((2*M)*w) := Nat.mul_le_mul_left T (Nat.mul_le_mul_right w hpad)
    _ = (2*T*w)*M := by ring

theorem move_volume_le (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) (k w : ℕ)
    (hpad : 2^k ≤ 2*localLength axis retained i) :
    moveVolume axis retained left i right k w ≤ 2*volume axis retained*w := by
  have hh := padded_volume_le _ _ k w _ (width_pos axis retained (.inr i))
    (movement_factorization axis retained left i right hn hall) hpad
  simpa only [moveVolume,Nat.mul_assoc] using hh

theorem halo_padded_volume_le (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) (k w : ℕ)
    (hpad : 2^k ≤ 2*localLength axis retained i) :
    ((haloBefore left).map (width axis retained)).prod*((axis i).N*
      (((haloMiddle left right).map (width axis retained)).prod*(2^k*w))) ≤ 2*volume axis retained*w := by
  have hh := padded_volume_le _ _ k w _ (width_pos axis retained (.inr i))
    (halo_factorization axis retained left i right hn hall) hpad
  simpa only [Nat.mul_assoc] using hh

theorem move_volume_least_le (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) (w : ℕ) :
    moveVolume axis retained left i right (Nat.clog 2 (localLength axis retained i)) w ≤ 2*volume axis retained*w :=
  move_volume_le axis retained left i right hn hall _ w
    (GeneratedFiberPadding.dyadic_capacity_bounds _ (width_pos axis retained (.inr i))).2.le

theorem count_products_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right) :
    (xs axis retained s).prod ≤ volume axis retained/localLength axis retained s.i ∧
    (ys axis retained s).prod ≤ volume axis retained/localLength axis retained s.i ∧
    (zs axis retained s).prod ≤ volume axis retained/localLength axis retained s.i := by
  have hM : 0 < localLength axis retained s.i := width_pos axis retained (Sum.inr s.i)
  have hmove := movement_factorization axis retained s.left s.i s.right hn hall
  have hhalo := halo_factorization axis retained s.left s.i s.right hn hall
  have hN := (axis s.i).N_pos
  have hP := product_pos axis retained (moveBefore s.left s.i s.right)
  have hB := product_pos axis retained (moveMiddle s.right)
  have hS := product_pos axis retained (haloMiddle s.left s.right)
  refine ⟨(Nat.le_div_iff_mul_le hM).mpr ?_,(Nat.le_div_iff_mul_le hM).mpr ?_,(Nat.le_div_iff_mul_le hM).mpr ?_⟩
  · rw [←hhalo]
    have hh := Nat.le_mul_of_pos_right ((xs axis retained s).prod*localLength axis retained s.i) (Nat.mul_pos hN hS)
    convert hh using 1; dsimp [xs]; ring
  · rw [←hmove]
    have hh := Nat.le_mul_of_pos_right ((ys axis retained s).prod*localLength axis retained s.i) hB
    convert hh using 1; dsimp [ys]; ring
  · rw [←hmove]
    have hh := Nat.le_mul_of_pos_left ((zs axis retained s).prod*localLength axis retained s.i) hP
    convert hh using 1; dsimp [zs]; ring

theorem move_volume_global_le (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) (k w L H : ℕ)
    (hpad : 2^k ≤ 2*localLength axis retained i)
    (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H) (hLpos : 0 < L)
    (hlarge : 64*Fintype.card ι*H ≤ L) :
    moveVolume axis retained left i right k w ≤ 4*volume axis ∅*w := by
  have hv := RetainedHaloVolume.volume_lt_two_of_large_core axis retained L H hL hH hLpos hlarge
  calc
    _ ≤ 2*volume axis retained*w := move_volume_le axis retained left i right hn hall k w hpad
    _ ≤ 2*(2*volume axis ∅)*w := Nat.mul_le_mul_right w (Nat.mul_le_mul_left 2 hv.le)
    _ = _ := by ring

theorem count_products_global_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hi : s.i ∉ retained) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L) :
    (xs axis retained s).prod ≤ (2*volume axis ∅)/L ∧
    (ys axis retained s).prod ≤ (2*volume axis ∅)/L ∧
    (zs axis retained s).prod ≤ (2*volume axis ∅)/L := by
  have hc := count_products_le axis retained s hn hall
  have hlocal : localLength axis retained s.i = L := by simp [localLength,hi,hL]
  rw [hlocal] at hc
  have hv := RetainedHaloVolume.volume_lt_two_of_large_core axis retained L H hL hH hLpos hlarge
  have hq : volume axis retained/L ≤ (2*volume axis ∅)/L := Nat.div_le_div_right hv.le
  exact ⟨hc.1.trans hq,hc.2.1.trans hq,hc.2.2.trans hq⟩

theorem page_count_le (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) :
    ((haloBefore left).map (width axis retained)).prod*(axis i).N ≤ volume axis retained/localLength axis retained i := by
  apply (Nat.le_div_iff_mul_le (show 0 < localLength axis retained i from width_pos axis retained (.inr i))).mpr
  rw [←halo_factorization axis retained left i right hn hall]
  have hh := Nat.le_mul_of_pos_right
    (((haloBefore left).map (width axis retained)).prod*(axis i).N*localLength axis retained i)
    (product_pos axis retained (haloMiddle left right))
  convert hh using 1; ring

end IntegerMultBounds.MathlibTM2.Routing.HaloMixedVolume
