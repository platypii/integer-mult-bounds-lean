module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloLocalPadding
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAmortizedCoreGeometry
public import IntegerMultBounds.NLogN.PhaseCellCoreDescriptors

/-! Global local-traffic accounting for the actual generated core halos.
Endpoint setup keys are not identified merely because movement lengths agree. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open scoped BigOperators

theorem haloVertices_card_eq {s : ℕ} [NeZero s] (a b : ℕ) (hb : b ≤ s) :
    (haloVertices s a b).card = b-a := by
  have hc : (haloVertices s a b).card = (Finset.Ico a b).card := by
    apply Finset.card_bij (fun i _ => i.val)
    · intro i hi
      exact Finset.mem_Ico.mpr ((mem_haloVertices a b i).mp hi)
    · intro i hi j hj he
      exact ZMod.val_injective s he
    · intro j hj
      have hj' := Finset.mem_Ico.mp hj
      have hv : (j : ZMod s).val = j := ZMod.val_natCast_of_lt (by omega)
      exact ⟨(j : ZMod s),(mem_haloVertices a b _).mpr (by simpa only [hv] using hj'),hv⟩
  simpa only [Nat.card_Ico] using hc

theorem coreHaloEndpoints_span_volume_le {s : ℕ} [NeZero s] (width band depth : ℕ)
    (hw : width ≤ s) (hr : depth*band ≤ width) :
    (∑ k ∈ (coreIndices s width).toFinset,
      ((coreHaloEndpoints s width k band depth).2-(coreHaloEndpoints s width k band depth).1)) ≤ 9*s := by
  have hc := coreHalo_volume_le_nine width band depth hw hr
  have he (k : ℕ) :
      (coreHaloEndpoints s width k band depth).2-(coreHaloEndpoints s width k band depth).1 =
        (coreHalo s width k band depth).card := by
    calc
      _ = (haloVertices s (coreHaloEndpoints s width k band depth).1
          (coreHaloEndpoints s width k band depth).2).card :=
        (haloVertices_card_eq _ _ (coreHaloEndpoints_bounds s width k band depth).2).symm
      _ = _ := congrArg Finset.card (coreHaloEndpoints_set width k band depth)
  exact (Finset.sum_congr rfl (fun k _ => he k)).le.trans hc

/-- The local padding envelope, before multiplication by the fixed program factor. -/
def haloLocalNativeVolume (s t band a b w : ℕ) : ℕ :=
  ((haloInterior s t band a b).card+8*(b-a)+8*(s/(t-s)+1))*w+6*((b-a)*w+1)

theorem haloLocalNativeVolume_le {s : ℕ} [NeZero s] (t band a b w : ℕ) :
    haloLocalNativeVolume s t band a b w ≤ 15*(b-a)*w+8*(s/(t-s)+1)*w+6 := by
  have hi := (Finset.card_le_card (haloInterior_subset s t band a b)).trans (haloVertices_card_le s a b)
  unfold haloLocalNativeVolume
  nlinarith only [Nat.mul_le_mul_right w hi]

/-- Overlap and endpoint slack together give linear line-volume traffic.
This includes seam fallbacks; numerical setup multiplicities remain separate. -/
theorem coreHalo_localNativeVolume_le {s : ℕ} [NeZero s] (t width band depth w : ℕ)
    (hwidth : 0 < width) (hw : width ≤ s) (hr : depth*band ≤ width)
    (hcell : s/(t-s)+1 ≤ width) (hword : 1 ≤ w) :
    (∑ k ∈ (coreIndices s width).toFinset,
      haloLocalNativeVolume s t band (coreHaloEndpoints s width k band depth).1
        (coreHaloEndpoints s width k band depth).2 w) ≤ 163*s*w := by
  let K := (coreIndices s width).toFinset
  let span := fun k => (coreHaloEndpoints s width k band depth).2-(coreHaloEndpoints s width k band depth).1
  have hv := coreHaloEndpoints_span_volume_le width band depth hw hr
  have hc : K.card*width ≤ 2*s := by
    simpa only [K,List.toFinset_card_of_nodup (coreIndices_nodup s width)] using coreSlots_le_two s width hw
  have hcount : K.card ≤ 2*s := (Nat.le_mul_of_pos_right K.card hwidth).trans hc
  have hslots : K.card*(s/(t-s)+1) ≤ 2*s := (Nat.mul_le_mul_left K.card hcell).trans hc
  have hsum : (∑ k ∈ K, haloLocalNativeVolume s t band
      (coreHaloEndpoints s width k band depth).1 (coreHaloEndpoints s width k band depth).2 w) ≤
      15*(∑ k ∈ K, span k)*w+8*(K.card*(s/(t-s)+1))*w+6*K.card := by
    calc
      _ ≤ ∑ k ∈ K, (15*span k*w+8*(s/(t-s)+1)*w+6) :=
        Finset.sum_le_sum (fun k _ => haloLocalNativeVolume_le _ _ _ _ _)
      _ = _ := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id]
        have he : (∑ k ∈ K, 15*span k*w) = (15*w)*(∑ k ∈ K, span k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        rw [he]
        ring
  have hvw := Nat.mul_le_mul_right w hv
  have hsw := Nat.mul_le_mul_right w hslots
  have hcountw : K.card ≤ 2*s*w := by nlinarith only [hcount,hword]
  change (∑ k ∈ K, _) ≤ _
  change (∑ k ∈ K, span k) ≤ 9*s at hv
  nlinarith only [hsum,hvw,hsw,hcountw]

/-- Aggregate the actual grouped repeated-traffic term over all core halos. -/
theorem coreHalo_groupedTraffic_le {s t : ℕ} [NeZero s] (hst : s < t) (hgap : t-s ≤ s)
    (width band depth w N F : ℕ) (hwidth : 0 < width) (hw : width ≤ s)
    (hr : depth*band ≤ width) (hcell : s/(t-s)+1 ≤ width) (hword : 1 ≤ w) :
    (∑ k ∈ (coreIndices s width).toFinset,
      let a := (coreHaloEndpoints s width k band depth).1
      let b := (coreHaloEndpoints s width k band depth).2
      ((haloLengthKeys s t band a b).map (fun L =>
        (F*N)*((haloLengthGroup s t band a b L).length*(L+2^haloInverseRingLog s t)*w+
          (b-a)*w+1))).sum) ≤ 163*F*N*s*w := by
  have hv := coreHalo_localNativeVolume_le t width band depth w hwidth hw hr hcell hword
  calc
    _ ≤ ∑ k ∈ (coreIndices s width).toFinset,
        (F*N)*haloLocalNativeVolume s t band (coreHaloEndpoints s width k band depth).1
          (coreHaloEndpoints s width k band depth).2 w := by
      apply Finset.sum_le_sum
      intro k hk
      exact haloLengthKeys_localTraffic_le hst hgap _ _ _ _ _
        (coreHaloEndpoints_bounds s width k band depth).1
    _ = (F*N)*(∑ k ∈ (coreIndices s width).toFinset,
        haloLocalNativeVolume s t band (coreHaloEndpoints s width k band depth).1
          (coreHaloEndpoints s width k band depth).2 w) := by rw [Finset.mul_sum]
    _ ≤ (F*N)*(163*s*w) := Nat.mul_le_mul_left _ hv
    _ = _ := by ring

/-- The selected p^8 cores absorb cell endpoint slack while retaining all seams. -/
theorem selectedCoreHalo_localNativeVolume_le (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target w : ℕ, target ≤ ct*Sizes.p n → 1 ≤ w →
      let width := amortizedCoreWidth ct (Sizes.p n)
      let band := PhaseCellBand.width (Sizes.p n) u
      let depth := localityDepth (Sizes.p n) target
      (∑ k ∈ (coreIndices (Sizes.s n i) width).toFinset,
        haloLocalNativeVolume (Sizes.s n i) (Sizes.t n i) band
          (coreHaloEndpoints (Sizes.s n i) width k band depth).1
          (coreHaloEndpoints (Sizes.s n i) width k band depth).2 w) ≤ 163*Sizes.s n i*w := by
  filter_upwards [selectedAmortizedCoreGeometry ct] with n hn
  intro h i _ u target w htarget hword
  dsimp only
  obtain ⟨hw,hwide,hguard,hroom,hlen⟩ := hn h i u target htarget
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hcell := phaseGap_cellLength_le hp (h.good.lt i) (h.quarter_p_le_theta i)
  have hpow : (Sizes.p n)^2 ≤ (Sizes.p n)^8 := pow_le_pow_right' hp (by decide)
  have hsmall : 4*Sizes.p n+1 ≤ (Sizes.p n)^2 := by
    have hh := h.thirteen_le_p
    nlinarith only [hh]
  apply coreHalo_localNativeVolume_le _ _ _ _ _ hw (by omega) hguard _ hword
  omega

end IntegerMultBounds.MathlibTM2.Cost
