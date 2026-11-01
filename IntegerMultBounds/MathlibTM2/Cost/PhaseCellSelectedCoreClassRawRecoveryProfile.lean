module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawRecoveryJobProfile
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreClassRecoveryTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreClassRecoveryStorage

/-! Construct the ordered raw jobs from mathematical halo bounds and discharge
all seven profile and geometry premises of the restoring scheduler together. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedCoreClassRawRecovery_profile (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target width L : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (hw : 0 < width) (hwidth : width ≤ Sizes.s n i)
    (hguard : localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u ≤ width)
    (hcell : Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width)
    (hprepare : (Sizes.p n)^2+(PhaseCellBand.width (Sizes.p n) u)^2 ≤ width)
    (α gap : ℝ) (C : ZMod (Sizes.s n i) → GaussianInt)
    (V : Fin (coreGatherIndices (Sizes.s n i) width
      (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices (Sizes.s n i) width
        (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L)[j.val]
      PackedHaloParameterBounds (p := Sizes.p n)
        (l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (t := Sizes.t n i)
        (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints (Sizes.s n i) width k (PhaseCellBand.width (Sizes.p n) u)
          (localityDepth (Sizes.p n) target)).1)
        (b := (coreHaloEndpoints (Sizes.s n i) width k (PhaseCellBand.width (Sizes.p n) u)
          (localityDepth (Sizes.p n) target)).2) (V := V j) α gap C)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p n) (F j)‖ ≤ 1) :
    let cH := 1032+8*ct
    let cw := 16*20+8*cH+8*2+128
    let cVratio := 2*cw+426009
    let W := packedHaloCommonWidth (Sizes.p n)
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) u (target+1) 2
    let jobs := fun j => RawRecoveryJob.ofComplexBounds (bounds j) Fs hF W
      (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
    let records := List.ofFn jobs
    records.length ≤ 2*Sizes.t n i ∧
    (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
      r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.problem.u ≤ r.problem.p ∧
      r.problem.l ≤ 20*r.problem.p ∧ r.problem.wordWidth ≤ cw*r.problem.p ∧
      2^r.problem.l ≤ 20*r.problem.p ∧ r.problem.metadataWidth ≤ (cVratio*cw)*r.problem.p ∧
      r.W ≤ cH*r.problem.p ∧ r.problem.rhsExp = 2 ∧ 1 ≤ r.target ∧ r.target ≤ ct*Sizes.p n+1) ∧
    (∀ r ∈ records, r.problem.metadataWidth ≤ cVratio*r.problem.wordWidth ∧
      r.problem.Fs.length = 2*Fs.length) ∧
    (records.map (fun r => replicaHaloLocalCoordinates r.problem)).sum ≤ 163*Sizes.s n i ∧
    (records.map (fun r => r.problem.span)).sum ≤ 9*Sizes.s n i ∧
    (∀ r ∈ records, r.problem.target ≤ cH*Sizes.p n) ∧
    (records.map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤
      600*(Sizes.s n i+(Sizes.t n i-Sizes.s n i)*(PhaseCellBand.width (Sizes.p n) u)^2) := by
  dsimp only
  let indices := coreGatherIndices (Sizes.s n i) width
    (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L
  let W := packedHaloCommonWidth (Sizes.p n)
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) u (target+1) 2
  let jobs := fun j => RawRecoveryJob.ofComplexBounds (bounds j) Fs hF W
    (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
  have hprofile (j : Fin indices.length) := selectedRawRecoveryJob_profile ct h i (bounds j) hu htarget Fs hF
  have hgeometry (j : Fin indices.length) := RawRecoveryJob.ofComplexBounds_profile (bounds j) Fs hF W
    (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · have hlength : indices.length ≤ (coreIndices (Sizes.s n i) width).length := List.length_filter_le _ _
    have hslots := coreSlots_le_two (Sizes.s n i) width hwidth
    have hcount := Nat.le_mul_of_pos_right (coreIndices (Sizes.s n i) width).length hw
    simp only [List.length_ofFn]
    change indices.length ≤ 2*Sizes.t n i
    have := h.good.lt i
    omega
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact (hprofile j).1
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact (hprofile j).2.1
  · apply coreClassJobCoordinateVolume_le width (PhaseCellBand.width (Sizes.p n) u)
      (localityDepth (Sizes.p n) target) L hw hwidth hguard hcell jobs
    intro j
    obtain ⟨_,_,ht,_,_,ha,hspan,hband,_⟩ := hgeometry j
    exact ⟨ht,hband,ha,hspan⟩
  · apply coreClassJobSpan_le width (PhaseCellBand.width (Sizes.p n) u)
      (localityDepth (Sizes.p n) target) L hwidth hguard jobs
    intro j
    exact (hgeometry j).2.2.2.2.2.2.1
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact (hprofile j).2.2
  · apply coreClassJobLocalVolume_le (h.good.lt i) (Sizes.p n) width
      (PhaseCellBand.width (Sizes.p n) u) (localityDepth (Sizes.p n) target) L
      hw hwidth hguard (PhaseCellBand.width_pos _ _) hcell hprepare jobs
    intro j
    obtain ⟨hp,_,ht,_,_,ha,hspan,hband,_⟩ := hgeometry j
    exact ⟨hp,ht,hband,ha,hspan⟩

end IntegerMultBounds.MathlibTM2.Cost
