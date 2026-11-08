module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMetadataFit

/-! Construct actual axis parameters from row geometry. Ordinary dimensions,
least exponents and one global encoded width determine all runtime metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloStageParameters
open HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule HaloMixedOrder HaloMixedVolume

/-- No fit certificate is supplied: both binary capacities follow from row size. -/
def ofRow (N L H B w T d : ℕ) (hN : 0 < N) (hL : 0 < L) (hB : 0 < B)
    (hw : 0 < w) (hgap : 2*H ≤ L) (hrow : N*L*B ≤ 2*T) : Parameters where
  N := N
  L := L
  H := H
  B := B
  w := w
  V := HaloMetadataFit.metadataWidth T w d
  k := Nat.clog 2 L
  r := Nat.clog 2 (L+2*H)
  N_pos := hN
  L_pos := hL
  B_pos := hB
  w_pos := hw
  gap := hgap
  capacity := Nat.le_pow_clog (by decide) _
  return_capacity := Nat.le_pow_clog (by decide) _
  fits := by
    have hcap : 8*T*w+2*d+1 ≤ 2^(HaloMetadataFit.metadataWidth T w d) :=
      Nat.le_pow_clog (by decide) _
    have hs := Nat.mul_le_mul_right w hrow
    have hNL : L ≤ N*L := Nat.le_mul_of_pos_left L hN
    have hh := Nat.mul_le_mul_right (B*w) (hgap.trans hNL)
    nlinarith only [hcap,hs,hh]
  count_fits := by
    have hcap : 8*T*w+2*d+1 ≤ 2^(HaloMetadataFit.metadataWidth T w d) :=
      Nat.le_pow_clog (by decide) _
    have hn : N ≤ N*L*B := (Nat.le_mul_of_pos_right N hL).trans (Nat.le_mul_of_pos_right _ hB)
    have hpos : 0 < N*L*B := Nat.mul_pos (Nat.mul_pos hN hL) hB
    have hT : 0 < T := by omega
    have hbytes := Nat.le_mul_of_pos_right T hw
    nlinarith only [hcap,hn,hrow,hT,hbytes]

variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem row_le (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) (hi : i ∉ retained) :
    (axis i).N*(axis i).L*((haloMiddle left right).map (width axis retained)).prod ≤ volume axis retained := by
  have hf := halo_factorization axis retained left i right hn hall
  have hp := product_pos axis retained (haloBefore left)
  simp only [localLength,ite_eq_right hi] at hf
  rw [←hf]
  have hh := Nat.le_mul_of_pos_left
    ((axis i).N*(axis i).L*((haloMiddle left right).map (width axis retained)).prod) hp
  convert hh using 1; ring

def parameters (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) (hi : i ∉ retained)
    (w : ℕ) (hw : 0 < w) (hgap : 2*(axis i).H ≤ (axis i).L)
    (hv : volume axis retained ≤ 2*volume axis ∅) : Parameters :=
  ofRow (axis i).N (axis i).L (axis i).H ((haloMiddle left right).map (width axis retained)).prod
    w (volume axis ∅) (left++i::right).length (axis i).N_pos (axis i).L_pos
    (product_pos axis retained _) hw hgap ((row_le axis retained left i right hn hall hi).trans hv)

def stage (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) (hi : i ∉ retained)
    (w : ℕ) (hw : 0 < w) (hgap : 2*(axis i).H ≤ (axis i).L)
    (hv : volume axis retained ≤ 2*volume axis ∅) : Stage ι where
  params := parameters axis retained left i right hn hall hi w hw hgap hv
  left := left
  i := i
  right := right

theorem stage_ready (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (hall : ∀ j, j ∈ left++i::right) (hi : i ∉ retained)
    (w : ℕ) (hw : 0 < w) (hgap : 2*(axis i).H ≤ (axis i).L)
    (hv : volume axis retained ≤ 2*volume axis ∅) :
    Ready axis retained (stage axis retained left i right hn hall hi w hw hgap hv) := by
  apply HaloMetadataFit.ready_global axis retained _ hn hall hi _ rfl hv rfl rfl rfl
  cases axis i
  rfl

end IntegerMultBounds.MathlibTM2.Routing.HaloStageParameters
