module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryScheduleTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreClassRecoveryVolume

/-! Ordered core-class jobs satisfy the complete raw-caller time estimate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem coreClassJobSpan_le {s : ℕ} [NeZero s] (width band n L : ℕ)
    (hwidth : width ≤ s) (hr : n*band ≤ width)
    (jobs : Fin (coreGatherIndices s width (n*band) L).length → RawRecoveryJob s)
    (hspan : ∀ i, let k := (coreGatherIndices s width (n*band) L)[i.val]
      (jobs i).problem.span = (coreHaloEndpoints s width k band n).2-(coreHaloEndpoints s width k band n).1) :
    ((List.ofFn jobs).map (fun r => r.problem.span)).sum ≤ 9*s := by
  let indices := coreGatherIndices s width (n*band) L
  let span := fun k => (coreHaloEndpoints s width k band n).2-(coreHaloEndpoints s width k band n).1
  have heq : (List.ofFn jobs).map (fun r => r.problem.span) = indices.map span := by
    rw [List.map_ofFn]
    calc
      _ = List.ofFn (fun i : Fin indices.length => span indices[i.val]) := by
        congr 1
        funext i
        exact hspan i
      _ = _ := List.ofFn_getElem_eq_map indices span
  have hnodup : indices.Nodup := (coreIndices_nodup s width).filter _
  have hsub : indices.toFinset ⊆ (coreIndices s width).toFinset := by
    intro k hk
    exact List.mem_toFinset.mpr ((List.mem_filter.mp (List.mem_toFinset.mp hk)).1)
  rw [heq,←List.sum_toFinset _ hnodup]
  exact (Finset.sum_le_sum_of_subset hsub).trans (coreHaloEndpoints_span_volume_le width band n hwidth hr)

/-- Mathematical constructor profiles and core geometry discharge the raw
caller time sum. Descriptor loading and cleanup are accounted for separately. -/
theorem selectedCoreClassRecovery_time_le (ct cH cW : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (width band depth L N : ℕ)
      (jobs : Fin (coreGatherIndices (Sizes.s n i) width (depth*band) L).length →
        RawRecoveryJob (Sizes.s n i))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution),
      0 < width → width ≤ Sizes.s n i → depth*band ≤ width → 1 ≤ band →
      Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width → (Sizes.p n)^2+band^2 ≤ width →
      (∀ j, (jobs j).problem.p = Sizes.p n ∧ (jobs j).problem.t = Sizes.t n i ∧
        (jobs j).problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        (jobs j).problem.u ≤ Sizes.p n ∧ (jobs j).problem.target ≤ cH*Sizes.p n ∧
        (jobs j).problem.rhsExp = 2 ∧ (jobs j).problem.Fs.length = N ∧
        1 ≤ (jobs j).target ∧ (jobs j).target ≤ ct*Sizes.p n+1 ∧ (jobs j).W ≤ cW*Sizes.p n) →
      (∀ j, let k := (coreGatherIndices (Sizes.s n i) width (depth*band) L)[j.val]
        (jobs j).problem.band = band ∧
        (jobs j).problem.origin = (coreHaloEndpoints (Sizes.s n i) width k band depth).1 ∧
        (jobs j).problem.span = (coreHaloEndpoints (Sizes.s n i) width k band depth).2-
          (coreHaloEndpoints (Sizes.s n i) width k band depth).1) →
      ((((List.ofFn jobs).map (fun r => r.runTime (B r))).sum : ℕ) : ℝ) ≤
        Sizes.T n+F*N*(Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hbound⟩ := selectedRawRecoverySchedule_density_time_le ct cH cW
  refine ⟨F,hF,?_⟩
  filter_upwards [hbound] with n htime
  intro h i _ width band depth L N jobs B hw hwidth hr hband hcell hprepare hparams hgeometry
  apply htime h i (List.ofFn jobs) B N band
  · have hlength : (coreGatherIndices (Sizes.s n i) width (depth*band) L).length ≤
        (coreIndices (Sizes.s n i) width).length := List.length_filter_le _ _
    have hslots := coreSlots_le_two (Sizes.s n i) width hwidth
    have hcount := Nat.le_mul_of_pos_right (coreIndices (Sizes.s n i) width).length hw
    simp only [List.length_ofFn]
    have := h.good.lt i
    omega
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact hparams j
  · apply coreClassJobSpan_le width band depth L hwidth hr jobs
    intro j
    exact (hgeometry j).2.2
  · apply coreClassJobLocalVolume_le (h.good.lt i) (Sizes.p n) width band depth L hw hwidth hr hband hcell hprepare jobs
    intro j
    exact ⟨(hparams j).1,(hparams j).2.1,(hgeometry j).1,(hgeometry j).2.1,(hgeometry j).2.2⟩

end IntegerMultBounds.MathlibTM2.Cost
