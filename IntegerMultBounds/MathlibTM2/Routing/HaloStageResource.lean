module

public import IntegerMultBounds.MathlibTM2.Routing.HaloSetupResource

/-! Full metadata-driven stage budgets in original tensor bytes. All setup,
movement, stream, restoration and retirement bills are included. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloStageResource
open HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule HaloMixedOrder HaloMixedOrderRun
  HaloMixedVolume HaloCountResource HaloStreamResource HaloPrefixResource HaloSetupResource

def countUnit (D V : ℕ) := 3*D*(19*V+88)+57*V+105
def timeUnit (k r V D : ℕ) := haloUnit V+3*k+3*r+220*V+792+3*D*(19*V+88)
def stockUnit (V D : ℕ) := 3*haloUnit V+594*V+1628+9*D*(19*V+88)

theorem counts_bytes_le (V w D Q : ℕ) (hw : 0 < w) (hQ : 0 < Q) (xs ys zs : List ℕ)
    (hD : xs.length ≤ D ∧ ys.length ≤ D ∧ zs.length ≤ D)
    (hprod : xs.prod ≤ Q ∧ ys.prod ≤ Q ∧ zs.prod ≤ Q) :
    HaloMixedCountHeaders.cost V xs ys zs ≤ (Q*w)*countUnit D V := by
  have hc := counts_cost_le V xs ys zs D Q hD hprod
  have hqw := Nat.le_mul_of_pos_right Q hw
  have hW := Nat.mul_pos hQ hw
  have hs := Nat.le_mul_of_pos_left (19*V+57) hW
  have hf : 31*Q+19*V+57 ≤ (Q*w)*(19*V+88) := by nlinarith only [hqw,hs]
  have hd := Nat.mul_le_mul_left D hf
  have ht := Nat.le_mul_of_pos_left (19*V+35) hW
  dsimp only [countUnit]
  nlinarith only [hc,hd,ht]

variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem mixed_bills_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L) (hcoarse : s.params.L ≤ s.params.N)
    (hk : 2^s.params.k ≤ 2*s.params.L) (hrpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H)) :
    let T := volume axis ∅
    let Q := (2*T)/L
    let Z := T*s.params.w
    let W := Q*s.params.w
    let a := moveVolume axis retained s.left s.i s.right s.params.k s.params.w
    let b := moveVolume axis (insert s.i retained) s.left s.i s.right s.params.r s.params.w
    HaloMixedAxis.cost s.params (xs axis retained s).prod a b ≤
      Z*(496*s.params.k+496*s.params.r+6652)+W*(haloUnit s.params.V+3*s.params.k+3*s.params.r+12*s.params.V+156)+18*s.params.V+180 ∧
    HaloMixedAxis.reserve s.params (xs axis retained s).prod a b ≤
      17318*Z+W*(3*haloUnit s.params.V+142)+24*s.params.V+268 := by
  have hb := bounds_global axis retained s hn hall hr L H hL hH hLpos hlarge hcoarse hk hrpad
  let T := volume axis ∅
  let Q := (2*T)/L
  let W := Q*s.params.w
  have hqw : Q ≤ W := Nat.le_mul_of_pos_right Q s.params.w_pos
  have hqpos : 0 < Q := lt_of_lt_of_le s.params.N_pos hb.count
  have hw : s.params.w ≤ W := Nat.le_mul_of_pos_left _ hqpos
  have hlength : s.params.L ≤ W := hb.length.trans hqw
  have hhalo : 2*s.params.H ≤ W := hb.doubleHalo.trans hqw
  have hek : s.params.k ≤ 2*W := hb.forwardExponent.trans (Nat.mul_le_mul_left 2 hqw)
  have her : s.params.r ≤ 4*W := hb.returnExponent.trans (Nat.mul_le_mul_left 4 hqw)
  have hTZ := Nat.le_mul_of_pos_right T s.params.w_pos
  have hM : localLength axis retained s.i = s.params.L := by simp [localLength,hr.fresh,hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hM' : localLength axis (insert s.i retained) s.i = s.params.L+2*s.params.H := by
    simp [localLength,hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have ha := move_volume_global_le axis retained s.left s.i s.right hn hall s.params.k s.params.w L H
    (by rw [hM]; exact hk) hL hH hLpos hlarge
  have ha' := Nat.mul_le_mul_left (64*s.params.k+384) ha
  have haS := Nat.mul_le_mul_left 1000 ha
  have ht := move_volume_global_le axis (insert s.i retained) s.left s.i s.right hn hall s.params.r s.params.w L H
    (by rw [hM']; exact hrpad) hL hH hLpos hlarge
  have ht' := Nat.mul_le_mul_left (60*s.params.r+384) ht
  have htS := Nat.mul_le_mul_left 1000 ht
  have hhead := header_cost_le _ _ _ hb
  have hheadS := header_stock_le _ _ _ hb
  have hsize := header_size_le _ _ _ hb
  have hwidth := width_cost_le _ _ _ hb
  have hscan := scan_cost_global_le axis retained s hn hall hr L H hL hH hLpos hlarge hk hrpad
  have hscanS := scan_stock_global_le axis retained s hn hall hr L H hL hH hLpos hlarge hk hrpad
  have hmeta := Nat.mul_le_mul_right (haloUnit s.params.V+3*s.params.k+3*s.params.r+15) hqw
  have hmetaS := Nat.mul_le_mul_right (3*haloUnit s.params.V+8) hqw
  dsimp only [T,Q,W] at *
  constructor
  · dsimp only [HaloMixedAxis.cost,HaloAxisFromDimensions.cost,HaloMixedReturn.cost]
    nlinarith only [ha',ht',hhead,hsize,hwidth,hscan,hmeta,hw,hlength,hhalo,hek,her,hTZ]
  · dsimp only [HaloMixedAxis.reserve,HaloAxisFromDimensions.reserve,HaloMixedReturn.reserve]
    nlinarith only [haS,htS,hheadS,hwidth,hscanS,hmetaS,hTZ]

theorem stage_bills_le (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L) (hcoarse : s.params.L ≤ s.params.N)
    (hk : 2^s.params.k ≤ 2*s.params.L) (hrpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H)) :
    time axis retained s ≤ (volume axis ∅*s.params.w)*(496*s.params.k+496*s.params.r+6652)+
      (((2*volume axis ∅)/L)*s.params.w)*timeUnit s.params.k s.params.r s.params.V (2*(s.left++s.i::s.right).length) ∧
    HaloAxisSchedule.reserve axis retained s ≤ 17318*(volume axis ∅*s.params.w)+
      (((2*volume axis ∅)/L)*s.params.w)*stockUnit s.params.V (2*(s.left++s.i::s.right).length) := by
  have hb := bounds_global axis retained s hn hall hr L H hL hH hLpos hlarge hcoarse hk hrpad
  let Q := (2*volume axis ∅)/L
  let W := Q*s.params.w
  have hqpos : 0 < Q := lt_of_lt_of_le s.params.N_pos hb.count
  have hWpos : 0 < W := Nat.mul_pos hqpos s.params.w_pos
  have hqw : Q ≤ W := Nat.le_mul_of_pos_right Q s.params.w_pos
  have hcount := counts_bytes_le s.params.V s.params.w _ Q s.params.w_pos hqpos
    (xs axis retained s) (ys axis retained s) (zs axis retained s)
    (factor_lengths axis retained s) (count_products_global_le axis retained s hn hall hr.fresh L H hL hH hLpos hlarge)
  have hcounts := count_products_global_le axis retained s hn hall hr.fresh L H hL hH hLpos hlarge
  have hmaster := master_cost_le _ _ _ hb
  have hsize := master_size_le _ _ _ hb
  have hbill := mixed_bills_le axis retained s hn hall hr L H hL hH hLpos hlarge hcoarse hk hrpad
  have hc : (xs axis retained s).prod+(ys axis retained s).prod+(zs axis retained s).prod ≤ 3*W := by
    rcases hcounts with ⟨hx,hy,hz⟩; omega
  dsimp only [Q,W] at *
  constructor
  · have hscalar := Nat.le_mul_of_pos_left (151*s.params.V+371) hWpos
    dsimp only [time,HaloMetadataAxis.cost,HaloCountedMixedAxis.cost]
    dsimp only [timeUnit,countUnit] at *
    nlinarith only [hmaster,hsize,hcount,hbill.1,hc,hscalar]
  · have hscalar := Nat.le_mul_of_pos_left (423*s.params.V+775) hWpos
    dsimp only [HaloAxisSchedule.reserve,HaloMetadataAxis.reserve,HaloCountedMixedAxis.reserve]
    dsimp only [stockUnit,countUnit] at *
    nlinarith only [hmaster,hcount,hbill.2,hscalar]

end IntegerMultBounds.MathlibTM2.Routing.HaloStageResource
