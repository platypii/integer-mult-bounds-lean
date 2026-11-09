module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreRecoveryLocalVolume
public import IntegerMultBounds.NLogN.PhaseCellCoreGather
import Mathlib.Tactic.Linarith

/-! A fitting cyclic window has an empty right interval. Its implementation
still pays scalar and phase-cell padding, once per core, which fits the same
core-width allowance as the nonempty intervals. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open scoped BigOperators

theorem emptyReplicaRecoveryLocalVolume_le {s : ℕ} [NeZero s]
    (H : ReplicaHaloProblem s) (width : ℕ) (hempty : H.span = 0)
    (hcell : s/(H.t-s)+1 ≤ width) (hprepare : H.p^2+H.band^2 ≤ width)
    (hband : 1 ≤ H.band) : replicaRecoveryLocalVolume H ≤ 40*width := by
  have hv : haloVertices s H.origin (H.origin+H.span) = ∅ := by
    simp only [hempty,Nat.add_zero,haloVertices]
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
    omega
  have hi : haloInterior s H.t H.band H.origin (H.origin+H.span) = ∅ :=
    Finset.subset_empty.mp ((haloInterior_subset s H.t H.band H.origin (H.origin+H.span)).trans hv.le)
  have hb : haloBoundary s H.t H.band H.origin (H.origin+H.span) = ∅ := by
    rw [haloBoundary,hv]; simp
  have hp : 1 ≤ width := (Nat.succ_le_succ (Nat.zero_le _)).trans hcell
  have hB : H.band ≤ H.band^2 := by nlinarith
  unfold replicaRecoveryLocalVolume replicaHaloLocalCoordinates retainedCouplingActiveRows
  rw [hi,hb,hempty]
  simp only [Finset.card_empty,Finset.range_zero,Finset.filter_empty,Nat.zero_add,
    Nat.add_zero,Nat.mul_zero,Nat.zero_mul,Nat.one_mul]
  nlinarith

/-- Empty right passes do not introduce a core-count factor into the axis bill. -/
theorem coreEmptyReplicaRecoveryLocalVolume_sum_le {s : ℕ} [NeZero s]
    (width : ℕ) (hwidth : width ≤ s) (H : ℕ → ReplicaHaloProblem s)
    (hparams : ∀ k ∈ coreIndices s width, (H k).span = 0 ∧
      s/((H k).t-s)+1 ≤ width ∧ (H k).p^2+(H k).band^2 ≤ width ∧ 1 ≤ (H k).band) :
    (∑ k ∈ (coreIndices s width).toFinset, replicaRecoveryLocalVolume (H k)) ≤ 80*s := by
  have hs : (∑ k ∈ (coreIndices s width).toFinset, replicaRecoveryLocalVolume (H k)) ≤
      (coreIndices s width).length*(40*width) := by
    calc
      _ ≤ ∑ _k ∈ (coreIndices s width).toFinset, 40*width := by
        apply Finset.sum_le_sum
        intro k hk
        obtain ⟨he,hc,hp,hb⟩ := hparams k (List.mem_toFinset.mp hk)
        exact emptyReplicaRecoveryLocalVolume_le (H k) width he hc hp hb
      _ = _ := by
        simp only [Finset.sum_const,nsmul_eq_mul,
          List.toFinset_card_of_nodup (coreIndices_nodup s width),Nat.cast_id]
  have hc := coreSlots_le_two s width hwidth
  nlinarith

/-- Both implemented passes fit one axis-volume allowance in the fitting case,
including the nonzero padding cost of every empty right pass. -/
theorem fittingCyclicReplicaRecoveryLocalVolume_sum_le {s t : ℕ} [NeZero s]
    (hst : s < t) (p width band depth : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hguard : depth*band ≤ width) (hband : 1 ≤ band)
    (hcell : s/(t-s)+1 ≤ width) (hprepare : p^2+band^2 ≤ width)
    (H K : ℕ → ReplicaHaloProblem s)
    (hH : ∀ k ∈ coreIndices s width, (H k).p = p ∧ (H k).t = t ∧
      (H k).band = band ∧ (H k).origin = (coreHaloEndpoints s width k band depth).1 ∧
      (H k).span = (coreHaloEndpoints s width k band depth).2-
        (coreHaloEndpoints s width k band depth).1)
    (hK : ∀ k ∈ coreIndices s width, (K k).span = 0 ∧ (K k).p = p ∧
      (K k).t = t ∧ (K k).band = band) :
    (∑ k ∈ (coreIndices s width).toFinset,
      (replicaRecoveryLocalVolume (H k)+replicaRecoveryLocalVolume (K k))) ≤
      680*(s+(t-s)*band^2) := by
  have hleft := coreReplicaRecoveryLocalVolume_amortized_le hst p width band depth
    hw hwidth hguard hband hcell hprepare H hH
  have hright := coreEmptyReplicaRecoveryLocalVolume_sum_le width hwidth K (by
    intro k hk
    obtain ⟨he,hp,ht,hb⟩ := hK k hk
    exact ⟨he,by simpa only [ht] using hcell,
      by simpa only [hp,hb] using hprepare,by simpa only [hb] using hband⟩)
  rw [Finset.sum_add_distrib]
  nlinarith

/-- The computed fitting length class discharges endpoint conversion and the
empty right-pass geometry directly from membership. -/
theorem computedFittingCyclicRecoveryLocalVolume_sum_le {s t : ℕ} [NeZero s]
    (hst : s < t) (p width band depth L : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hguard : depth*band ≤ width) (hband : 1 ≤ band)
    (hcell : s/(t-s)+1 ≤ width) (hprepare : p^2+band^2 ≤ width)
    (H K : ℕ → ReplicaHaloProblem s)
    (hparams : ∀ k ∈ coreGatherIndices s width (depth*band) L,
      (H k).p = p ∧ (H k).t = t ∧ (H k).band = band ∧
      (H k).origin = coreStart width k-depth*band ∧
      (H k).span = min L (s-(coreStart width k-depth*band)) ∧
      (K k).p = p ∧ (K k).t = t ∧ (K k).band = band ∧
      (K k).span = L-min L (s-(coreStart width k-depth*band))) :
    ((coreGatherIndices s width (depth*band) L).map (fun k =>
      replicaRecoveryLocalVolume (H k)+replicaRecoveryLocalVolume (K k))).sum ≤
      680*(s+(t-s)*band^2) := by
  let indices := coreGatherIndices s width (depth*band) L
  let V := fun k => haloRecoveryLocalVolume p s t band
    (coreHaloEndpoints s width k band depth).1 (coreHaloEndpoints s width k band depth).2
  have hsub : indices.toFinset ⊆ (coreIndices s width).toFinset := by
    intro k hk
    exact List.mem_toFinset.mpr (List.mem_filter.mp (List.mem_toFinset.mp hk)).1
  have hn : indices.Nodup := (coreIndices_nodup s width).filter _
  have hcost : ∀ k ∈ indices, replicaRecoveryLocalVolume (H k)+
      replicaRecoveryLocalVolume (K k) ≤ V k+40*width := by
    intro k hk
    obtain ⟨hl,hr,hL⟩ := coreGatherIndices_spec s width (depth*band) L k hk
    obtain ⟨hpH,htH,hbH,haH,hsH,hpK,htK,hbK,hsK⟩ := hparams k hk
    have hfit : L ≤ s-(coreStart width k-depth*band) := by omega
    rw [min_eq_left hfit] at hsH hsK
    have he : coreHaloEndpoints s width k band depth =
        (coreStart width k-depth*band,coreStart width k+coreLength s width k+depth*band) := by
      simp only [coreHaloEndpoints,hl,hr,and_self,ite_true]
    have hv : replicaRecoveryLocalVolume (H k) = V k := by
      rw [replicaRecoveryLocalVolume_eq_halo,hpH,htH,hbH,haH,hsH]
      dsimp only [V]
      rw [he]
      congr 1
      dsimp only
      omega
    have hempty : (K k).span = 0 := by omega
    have hkcost := emptyReplicaRecoveryLocalVolume_le (K k) width hempty
      (by simpa only [htK] using hcell) (by simpa only [hpK,hbK] using hprepare)
      (by simpa only [hbK] using hband)
    rw [hv]
    exact Nat.add_le_add_left hkcost _
  rw [←List.sum_toFinset _ hn]
  have hsum := Finset.sum_le_sum (fun k hk => hcost k (List.mem_toFinset.mp hk))
  have hvol := (Finset.sum_le_sum_of_subset hsub :
    (∑ k ∈ indices.toFinset, V k) ≤ ∑ k ∈ (coreIndices s width).toFinset, V k)
  have haxis := coreHalo_recoveryLocalVolume_amortized_le hst p width band depth
    hw hwidth hguard hband hcell hprepare
  have hcount : indices.toFinset.card ≤ (coreIndices s width).length :=
    (Finset.card_le_card hsub).trans_eq (List.toFinset_card_of_nodup (coreIndices_nodup s width))
  have hslots := coreSlots_le_two s width hwidth
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at hsum
  change (∑ k ∈ indices.toFinset, _) ≤ _
  rw [Finset.sum_add_distrib]
  dsimp only [V] at hvol hsum
  nlinarith [Nat.mul_le_mul_right width hcount]

end IntegerMultBounds.MathlibTM2.Cost
