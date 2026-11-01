module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawRecoveryCoordinateStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreLocalStock

/-! Core-class storage is linear in the ambient packed line, without the
sparse boundary-work multiplier used in time estimates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- The native traffic envelope at unit symbol width is exactly the coordinate
storage envelope already used by both interior passes. -/
theorem replicaHaloLocalCoordinates_eq_native {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    replicaHaloLocalCoordinates H = haloLocalNativeVolume s H.t H.band H.origin (H.origin+H.span) 1 := by
  simp only [replicaHaloLocalCoordinates,haloLocalNativeVolume,Nat.add_sub_cancel_left,Nat.mul_one]

theorem coreClassJobCoordinateVolume_le {s t : ℕ} [NeZero s] (width band depth L : ℕ)
    (hw : 0 < width) (hwidth : width ≤ s) (hr : depth*band ≤ width) (hcell : s/(t-s)+1 ≤ width)
    (jobs : Fin (coreGatherIndices s width (depth*band) L).length → RawRecoveryJob s)
    (hparams : ∀ j, let k := (coreGatherIndices s width (depth*band) L)[j.val]
      (jobs j).problem.t = t ∧ (jobs j).problem.band = band ∧
      (jobs j).problem.origin = (coreHaloEndpoints s width k band depth).1 ∧
      (jobs j).problem.span = (coreHaloEndpoints s width k band depth).2-(coreHaloEndpoints s width k band depth).1) :
    ((List.ofFn jobs).map (fun r => replicaHaloLocalCoordinates r.problem)).sum ≤ 163*s := by
  let indices := coreGatherIndices s width (depth*band) L
  let volume := fun k => haloLocalNativeVolume s t band
    (coreHaloEndpoints s width k band depth).1 (coreHaloEndpoints s width k band depth).2 1
  have heq : (List.ofFn jobs).map (fun r => replicaHaloLocalCoordinates r.problem) = indices.map volume := by
    rw [List.map_ofFn]
    calc
      _ = List.ofFn (fun j : Fin indices.length => volume indices[j.val]) := by
        congr 1
        funext j
        change replicaHaloLocalCoordinates (jobs j).problem = volume indices[j.val]
        obtain ⟨ht,hB,ha,hspan⟩ := hparams j
        rw [replicaHaloLocalCoordinates_eq_native,ht,hB,ha,hspan,
          Nat.add_sub_of_le (coreHaloEndpoints_bounds s width indices[j.val] band depth).1]
      _ = _ := List.ofFn_getElem_eq_map indices volume
  have hnodup : indices.Nodup := (coreIndices_nodup s width).filter _
  have hsub : indices.toFinset ⊆ (coreIndices s width).toFinset := by
    intro k hk
    exact List.mem_toFinset.mpr ((List.mem_filter.mp (List.mem_toFinset.mp hk)).1)
  rw [heq,←List.sum_toFinset _ hnodup]
  have hs := coreHalo_localNativeVolume_le t width band depth 1 hw hwidth hr hcell (by decide)
  exact (Finset.sum_le_sum_of_subset hsub).trans (by simpa only [Nat.mul_one] using hs)

theorem rawRecoverySchedule_outputVolume_le {s : ℕ} [NeZero s]
    (records : List (RawRecoveryJob s)) (N p cw spanVolume : ℕ)
    (hparams : ∀ r ∈ records, r.problem.Fs.length = N ∧ r.problem.wordWidth ≤ cw*p)
    (hspan : (records.map (fun r => r.problem.span)).sum ≤ spanVolume) :
    (records.map RawRecoveryJob.outputVolume).sum ≤ cw*N*spanVolume*p := by
  have hs : (records.map RawRecoveryJob.outputVolume).sum ≤
      (records.map (fun r => (cw*N*p)*r.problem.span)).sum := by
    apply List.sum_le_sum
    intro r hr
    obtain ⟨hN,hw⟩ := hparams r hr
    have hh := Nat.mul_le_mul_left (N*r.problem.span) hw
    change r.problem.Fs.length*(r.problem.span*r.problem.wordWidth) ≤ _
    rw [hN]
    nlinarith only [hh]
  rw [List.sum_map_mul_left] at hs
  have hv := Nat.mul_le_mul_left (cw*N*p) hspan
  nlinarith only [hs,hv]

end IntegerMultBounds.MathlibTM2.Cost
