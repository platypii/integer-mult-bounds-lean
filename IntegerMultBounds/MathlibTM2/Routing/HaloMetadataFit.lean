module

public import IntegerMultBounds.MathlibTM2.Routing.HaloSetupResource

/-! Derive runtime metadata fit from ordinary geometry and one global capacity.
The parameter contract already bounds every ordinary master except exponents. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMetadataFit
open HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule HaloMixedOrder HaloMixedVolume

theorem masters_fit (p : Parameters) (hk : p.k < 2^p.V) (hr : p.r < 2^p.V) :
    ∀ e ∈ HaloAxisMasterSetup.entries p, e.2 < 2^p.V := by
  have hNL : 0 < p.N*p.L := Nat.mul_pos p.N_pos p.L_pos
  have hrow : 0 < p.N*p.L*p.B := Nat.mul_pos hNL p.B_pos
  have hfull : p.N*p.L*p.B*p.w < 2^p.V := by
    apply lt_of_le_of_lt _ p.fits
    have hh := Nat.mul_le_mul_right (p.B*p.w) (show p.N*p.L ≤ p.N*p.L+2*p.H by omega)
    convert hh using 1; ring
  have hn : p.N ≤ p.N*p.L*p.B*p.w :=
    ((Nat.le_mul_of_pos_right p.N p.L_pos).trans (Nat.le_mul_of_pos_right _ p.B_pos)).trans
      (Nat.le_mul_of_pos_right _ p.w_pos)
  have hl : p.L ≤ p.N*p.L*p.B*p.w :=
    ((Nat.le_mul_of_pos_left p.L p.N_pos).trans (Nat.le_mul_of_pos_right _ p.B_pos)).trans
      (Nat.le_mul_of_pos_right _ p.w_pos)
  have hb : p.B ≤ p.N*p.L*p.B*p.w :=
    (Nat.le_mul_of_pos_left p.B hNL).trans (Nat.le_mul_of_pos_right _ p.w_pos)
  have hw : p.w ≤ p.N*p.L*p.B*p.w := Nat.le_mul_of_pos_left p.w hrow
  have hh : p.H ≤ p.N*p.L*p.B*p.w := by have hg := p.gap; omega
  intro e he
  simp only [HaloAxisMasterSetup.entries,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hn.trans_lt hfull
  · exact hb.trans_lt hfull
  · exact hl.trans_lt hfull
  · exact hh.trans_lt hfull
  · exact hw.trans_lt hfull
  · exact hk
  · exact hr

variable {ι : Type} [DecidableEq ι] [Fintype ι]

omit [Fintype ι] in
private theorem mapped_factors_fit (axis : ι → Axis) (retained : Finset ι)
    (fields : List (Sum ι ι)) (C : ℕ) (hprod : (fields.map (width axis retained)).prod < C) :
    ∀ x ∈ fields.map (width axis retained), x < C := by
  intro x hx
  apply lt_of_le_of_lt _ hprod
  apply List.single_le_prod _ x hx
  intro y hy
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
  exact HaloMixedOrder.width_pos axis retained j

theorem ready_of_geometry (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hfresh : s.i ∉ retained) (haxis : axis s.i = HaloAxisTensorInvariant.axisOf s.params)
    (hspectator : ((haloMiddle s.left s.right).map (width axis retained)).prod = s.params.B)
    (hk : s.params.k < 2^s.params.V) (hr : s.params.r < 2^s.params.V)
    (hvolume : volume axis retained < 2^s.params.V)
    (hlength : 2*(s.left++s.i::s.right).length < 2^s.params.V) : Ready axis retained s := by
  have hp := count_products_le axis retained s hn hall
  have hd : volume axis retained/localLength axis retained s.i ≤ volume axis retained := Nat.div_le_self _ _
  have hx := mapped_factors_fit axis retained (haloBefore s.left) _ (hp.1.trans_lt (hd.trans_lt hvolume))
  have hy := mapped_factors_fit axis retained (moveBefore s.left s.i s.right) _ (hp.2.1.trans_lt (hd.trans_lt hvolume))
  have hz := mapped_factors_fit axis retained (moveMiddle s.right) _ (hp.2.2.trans_lt (hd.trans_lt hvolume))
  have hl := HaloCountResource.factor_lengths axis retained s
  refine ⟨hfresh,haxis,hspectator,masters_fit s.params hk hr,?_,?_⟩
  · intro x hmem
    simp only [List.mem_append] at hmem
    rcases hmem with (hmem | hmem) | hmem
    · exact hx x hmem
    · exact hy x hmem
    · exact hz x hmem
  · intro ds hds
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hds
    rcases hds with rfl | rfl | rfl
    · exact hl.1.trans_lt hlength
    · exact hl.2.1.trans_lt hlength
    · exact hl.2.2.trans_lt hlength

/-- One encoded width covers every retained stage and packet length. -/
def metadataWidth (T w d : ℕ) := Nat.clog 2 (8*T*w+2*d+1)

/-- A global tensor byte bound needs only four extra metadata bits. -/
theorem metadataWidth_le (T w d n : ℕ) (hpos : 0 < T*w) (hd : d ≤ T*w)
    (hbytes : T*w ≤ 2^n) : metadataWidth T w d ≤ n+4 := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  norm_num
  nlinarith only [hpos,hd,hbytes]

theorem ready_global (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hfresh : s.i ∉ retained) (haxis : axis s.i = HaloAxisTensorInvariant.axisOf s.params)
    (hspectator : ((haloMiddle s.left s.right).map (width axis retained)).prod = s.params.B)
    (hvolume : volume axis retained ≤ 2*volume axis ∅)
    (hV : s.params.V = metadataWidth (volume axis ∅) s.params.w (s.left++s.i::s.right).length)
    (hk : s.params.k = Nat.clog 2 s.params.L)
    (hr : s.params.r = Nat.clog 2 (s.params.L+2*s.params.H)) : Ready axis retained s := by
  have hM : localLength axis retained s.i = s.params.L := by
    simp [localLength,hfresh,haxis,HaloAxisTensorInvariant.axisOf]
  have hN : (axis s.i).N = s.params.N := by simp only [haxis,HaloAxisTensorInvariant.axisOf]
  have hf := halo_factorization axis retained s.left s.i s.right hn hall
  rw [hM,hN,hspectator] at hf
  have hp := product_pos axis retained (haloBefore s.left)
  have hrow : s.params.N*s.params.L*s.params.B ≤ volume axis retained := by
    rw [←hf]
    have hh := Nat.le_mul_of_pos_left (s.params.N*s.params.L*s.params.B) hp
    convert hh using 1; ring
  have hL : s.params.L ≤ 2*volume axis ∅ :=
    ((Nat.le_mul_of_pos_left s.params.L s.params.N_pos).trans
      (Nat.le_mul_of_pos_right _ s.params.B_pos)).trans (hrow.trans hvolume)
  have hbytes : volume axis ∅ ≤ volume axis ∅*s.params.w :=
    Nat.le_mul_of_pos_right _ s.params.w_pos
  have hcap : 8*volume axis ∅*s.params.w+2*(s.left++s.i::s.right).length+1 ≤ 2^s.params.V := by
    rw [hV]
    exact Nat.le_pow_clog (by decide) _
  have hsmall : s.params.k ≤ 2*s.params.L := by
    have hpad : 2^s.params.k ≤ 2*s.params.L := by
      rw [hk]
      exact (GeneratedFiberPadding.dyadic_capacity_bounds _ s.params.L_pos).2.le
    exact (HaloSetupResource.self_le_two_pow s.params.k).trans hpad
  have hreturn : s.params.r ≤ 4*s.params.L := by
    have hpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H) := by
      rw [hr]
      exact (GeneratedFiberPadding.dyadic_capacity_bounds _ (by have := s.params.L_pos; omega)).2.le
    have hh := (HaloSetupResource.self_le_two_pow s.params.r).trans hpad
    have hg := s.params.gap
    omega
  apply ready_of_geometry axis retained s hn hall hfresh haxis hspectator
  · nlinarith only [hsmall,hL,hbytes,hcap]
  · nlinarith only [hreturn,hL,hbytes,hcap]
  · nlinarith only [hvolume,hbytes,hcap]
  · omega

end IntegerMultBounds.MathlibTM2.Routing.HaloMetadataFit
