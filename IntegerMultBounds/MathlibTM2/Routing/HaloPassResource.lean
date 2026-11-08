module

public import IntegerMultBounds.MathlibTM2.Routing.HaloStreamResource

/-! Price the executed forward/halo/return body in the original tensor bytes.
Metadata is charged per coarse page; neither padding nor retained axes multiply
that charge by an artificial product of dyadic capacities. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloPassResource
open HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule HaloMixedOrder HaloMixedVolume
  HaloStreamResource HaloCoordinateLayout
variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem padded_volumes_global_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L)
    (hk : 2^s.params.k ≤ 2*s.params.L) (hrpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H)) :
    (xs axis retained s).prod*forwardVolume s.params ≤ 4*volume axis ∅*s.params.w ∧
    (xs axis retained s).prod*returnVolume s.params ≤ 4*volume axis ∅*s.params.w := by
  have hfields := fields_fresh s.left s.i s.right hn
  have hN : (axis s.i).N = s.params.N := by simp only [hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hM : localLength axis retained s.i = s.params.L := by
    simp [localLength,hr.fresh,hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hM' : localLength axis (insert s.i retained) s.i = s.params.L+2*s.params.H := by
    simp [localLength,hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hforward := halo_padded_volume_le axis retained s.left s.i s.right hn hall s.params.k s.params.w
    (by rw [hM]; exact hk)
  have hreturn := halo_padded_volume_le axis (insert s.i retained) s.left s.i s.right hn hall s.params.r s.params.w
    (by rw [hM']; exact hrpad)
  rw [hN,hr.spectator] at hforward
  rw [map_width_insert axis retained s.i _ hfields.2.2.1,
    map_width_insert axis retained s.i _ hfields.2.2.2,hN,hr.spectator] at hreturn
  have hv := RetainedHaloVolume.volume_lt_two_of_large_core axis retained L H hL hH hLpos hlarge
  have hv' := RetainedHaloVolume.volume_lt_two_of_large_core axis (insert s.i retained) L H hL hH hLpos hlarge
  constructor
  · change _ ≤ _ at hforward
    calc
      _ ≤ 2*volume axis retained*s.params.w := hforward
      _ ≤ 2*(2*volume axis ∅)*s.params.w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hv.le)
      _ = _ := by ring
  · calc
      _ ≤ 2*volume axis (insert s.i retained)*s.params.w := hreturn
      _ ≤ 2*(2*volume axis ∅)*s.params.w := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hv'.le)
      _ = _ := by ring

theorem pass_cost_global_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L)
    (hk : 2^s.params.k ≤ 2*s.params.L) (hrpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H)) :
    (xs axis retained s).prod*passCost s.params ≤
      (240*s.params.k+256*s.params.r+3392)*(volume axis ∅*s.params.w)+
        ((2*volume axis ∅)/L)*(haloUnit s.params.V+3*s.params.k+3*s.params.r+4) := by
  obtain ⟨hf,ht⟩ := padded_volumes_global_le axis retained s hn hall hr L H hL hH hLpos hlarge hk hrpad
  have hc := halo_cost_global_le axis retained s hn hall hr L H hL hH hLpos hlarge
  have hp := (count_products_global_le axis retained s hn hall hr.fresh L H hL hH hLpos hlarge).1
  have hf' := Nat.mul_le_mul_left (60*s.params.k+384) hf
  have ht' := Nat.mul_le_mul_left (64*s.params.r+384) ht
  have hp' := Nat.mul_le_mul_right (3*s.params.k+3*s.params.r+4) hp
  dsimp only [passCost]
  nlinarith only [hf',ht',hp',hc]

theorem pass_stock_global_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L)
    (hk : 2^s.params.k ≤ 2*s.params.L) (hrpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H)) :
    (xs axis retained s).prod*passStock s.params ≤
      8960*(volume axis ∅*s.params.w)+3*((2*volume axis ∅)/L)*haloUnit s.params.V := by
  obtain ⟨hf,ht⟩ := padded_volumes_global_le axis retained s hn hall hr L H hL hH hLpos hlarge hk hrpad
  have hc := Nat.mul_le_mul_left 3 (halo_cost_global_le axis retained s hn hall hr L H hL hH hLpos hlarge)
  have hf' := Nat.mul_le_mul_left 1000 hf
  have ht' := Nat.mul_le_mul_left 1000 ht
  dsimp only [passStock]
  nlinarith only [hf',ht',hc]

theorem output_bytes_eq (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right) (hr : Ready axis retained s) :
    (xs axis retained s).prod*outputVolume s.params = volume axis (insert s.i retained)*s.params.w := by
  have hfields := fields_fresh s.left s.i s.right hn
  have hN : (axis s.i).N = s.params.N := by simp only [hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hM : localLength axis (insert s.i retained) s.i = s.params.L+2*s.params.H := by
    simp [localLength,hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have he := halo_factorization axis (insert s.i retained) s.left s.i s.right hn hall
  rw [map_width_insert axis retained s.i _ hfields.2.2.1,
    map_width_insert axis retained s.i _ hfields.2.2.2,hN,hr.spectator,hM] at he
  dsimp only [xs,outputVolume]
  rw [←he]
  ring

end IntegerMultBounds.MathlibTM2.Routing.HaloPassResource
