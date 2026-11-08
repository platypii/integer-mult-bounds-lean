module

public import IntegerMultBounds.MathlibTM2.Routing.HaloPassResource

/-! The actual ordered prefix scan is priced in the global real tensor bytes.
Its stage reserve is reused, while output growth is its exact retained volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloPrefixResource
open HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule HaloMixedOrder HaloMixedVolume
  HaloStreamResource HaloPassResource
variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem scan_geometry_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L) :
    outputVolume s.params ≤ 2*(volume axis ∅*s.params.w) ∧
    (xs axis retained s).prod*outputVolume s.params ≤ 2*(volume axis ∅*s.params.w) ∧
    (xs axis retained s).prod ≤ (2*volume axis ∅)/L := by
  have hv := RetainedHaloVolume.volume_lt_two_of_large_core axis (insert s.i retained) L H hL hH hLpos hlarge
  have hfull : (xs axis retained s).prod*outputVolume s.params ≤ 2*(volume axis ∅*s.params.w) := by
    rw [output_bytes_eq axis retained s hn hall hr]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right s.params.w hv.le
  have hp : 0 < (xs axis retained s).prod := product_pos axis retained (haloBefore s.left)
  exact ⟨(Nat.le_mul_of_pos_left _ hp).trans hfull,hfull,
    (count_products_global_le axis retained s hn hall hr.fresh L H hL hH hLpos hlarge).1⟩

theorem scan_cost_global_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L)
    (hk : 2^s.params.k ≤ 2*s.params.L) (hrpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H)) :
    PreparedHaloPrefixScan.cost s.params (xs axis retained s).prod ≤
      (240*s.params.k+256*s.params.r+3494)*(volume axis ∅*s.params.w)+
        ((2*volume axis ∅)/L)*(haloUnit s.params.V+3*s.params.k+3*s.params.r+15)+35 := by
  have hs := scan_geometry_le axis retained s hn hall hr L H hL hH hLpos hlarge
  have hc := pass_cost_global_le axis retained s hn hall hr L H hL hH hLpos hlarge hk hrpad
  have h1 := Nat.mul_le_mul_left 45 hs.1
  have h2 := Nat.mul_le_mul_left 6 hs.2.1
  have h3 := Nat.mul_le_mul_left 11 hs.2.2
  dsimp only [PreparedHaloPrefixScan.cost,HaloArchiveFiber.cost]
  nlinarith only [hc,h1,h2,h3]

theorem scan_stock_global_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L)
    (hk : 2^s.params.k ≤ 2*s.params.L) (hrpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H)) :
    PreparedHaloPrefixScan.reserve s.params (xs axis retained s).prod ≤
      9154*(volume axis ∅*s.params.w)+((2*volume axis ∅)/L)*(3*haloUnit s.params.V+8)+68 := by
  have hs := scan_geometry_le axis retained s hn hall hr L H hL hH hLpos hlarge
  have hp : 0 < (xs axis retained s).prod := product_pos axis retained (haloBefore s.left)
  have hpass := (Nat.le_mul_of_pos_left (passStock s.params) hp).trans
    (pass_stock_global_le axis retained s hn hall hr L H hL hH hLpos hlarge hk hrpad)
  have h1 := Nat.mul_le_mul_left 94 hs.1
  have h2 := Nat.mul_le_mul_left 3 hs.2.1
  have h3 := Nat.mul_le_mul_left 8 hs.2.2
  dsimp only [PreparedHaloPrefixScan.reserve,HaloArchiveFiber.reserve]
  nlinarith only [hpass,h1,h2,h3]

end IntegerMultBounds.MathlibTM2.Routing.HaloPrefixResource
