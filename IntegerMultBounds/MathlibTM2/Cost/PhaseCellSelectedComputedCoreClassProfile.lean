module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreClassRawRecoveryProfile
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreWidths
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreJobRawRecovery

/-! Proper-core class jobs inherit the existing selected raw profiles and
volume estimates, and derive ordinary scalar/common-width setup bounds. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedCoreClassComputed_profile {A : ℕ} (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
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
    let indices := coreGatherIndices (Sizes.s n i) width (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L
    let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target
      (Sizes.t n i) width indices[j.val] (V j) α gap C Fs (bounds j) hF
    let records := List.ofFn jobs
    records.length ≤ 2*Sizes.t n i ∧
    (∀ r ∈ records, r.rawRecoveryJob.problem.p = Sizes.p n ∧ r.rawRecoveryJob.problem.t = Sizes.t n i ∧
      r.rawRecoveryJob.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧ r.rawRecoveryJob.problem.u ≤ r.rawRecoveryJob.problem.p ∧
      r.rawRecoveryJob.problem.l ≤ 20*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.wordWidth ≤ cw*r.rawRecoveryJob.problem.p ∧
      2^r.rawRecoveryJob.problem.l ≤ 20*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.metadataWidth ≤ (cVratio*cw)*r.rawRecoveryJob.problem.p ∧
      r.rawRecoveryJob.W ≤ cH*r.rawRecoveryJob.problem.p ∧ r.rawRecoveryJob.problem.rhsExp = 2 ∧ 1 ≤ r.rawRecoveryJob.target ∧ r.rawRecoveryJob.target ≤ ct*Sizes.p n+1) ∧
    (∀ r ∈ records, r.rawRecoveryJob.problem.metadataWidth ≤ cVratio*r.rawRecoveryJob.problem.wordWidth ∧
      r.rawRecoveryJob.problem.Fs.length = 2*Fs.length) ∧
    (records.map (fun r => replicaHaloLocalCoordinates r.rawRecoveryJob.problem)).sum ≤ 163*Sizes.s n i ∧
    (records.map (fun r => r.rawRecoveryJob.problem.span)).sum ≤ 9*Sizes.s n i ∧
    (∀ r ∈ records, r.rawRecoveryJob.problem.target ≤ cH*Sizes.p n) ∧
    (records.map (fun r => replicaRecoveryLocalVolume r.rawRecoveryJob.problem)).sum ≤
      600*(Sizes.s n i+(Sizes.t n i-Sizes.s n i)*(PhaseCellBand.width (Sizes.p n) u)^2) ∧
    (∀ r ∈ records, r.Fs = Fs ∧
      r.t = Sizes.t n i ∧ r.Bcore ≤ (2*(ct+21)+22+cH+ct+20)*Sizes.p n ∧
      r.p ≤ (2*(ct+21)+22+cH+ct+20)*Sizes.p n ∧ r.u ≤ (2*(ct+21)+22+cH+ct+20)*Sizes.p n ∧
      r.l ≤ (2*(ct+21)+22+cH+ct+20)*Sizes.p n ∧ r.targetOut ≤ (2*(ct+21)+22+cH+ct+20)*Sizes.p n ∧
      r.W ≤ (2*(ct+21)+22+cH+ct+20)*Sizes.p n ∧
      PhaseCellBand.width r.p r.u ≤ (2*(ct+21)+22+cH+ct+20)*Sizes.p n ∧
      2*r.q+8 ≤ (2*(ct+21)+22+cH+ct+20)*Sizes.p n) := by
  dsimp only
  let indices := coreGatherIndices (Sizes.s n i) width (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L
  let W := packedHaloCommonWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    (Sizes.s n i) u (target+1) 2
  let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := A) (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target
      (Sizes.t n i) width indices[j.val] (V j) α gap C Fs (bounds j) hF
  let rawJobs := fun j : Fin indices.length => RawRecoveryJob.ofComplexBounds (bounds j) Fs hF W
    (packedHaloCommonWidth_fits _ _ _ _ _ _ _ _ _)
  have hfun : (fun j : Fin indices.length => (jobs j).rawRecoveryJob) = rawJobs :=
    funext (fun j => PackedNormalizedJob.ofCoreCommon_rawRecoveryJob _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  have hmap : (List.ofFn jobs).map PackedNormalizedJob.rawRecoveryJob = List.ofFn rawJobs := by
    simpa only [List.map_ofFn,Function.comp_def] using congrArg List.ofFn hfun
  have hsum (f : RawRecoveryJob (Sizes.s n i) → ℕ) :
      ((List.ofFn jobs).map (fun r => f r.rawRecoveryJob)).sum = ((List.ofFn rawJobs).map f).sum := by
    simpa only [List.map_map,Function.comp_def] using congrArg (fun rs => (rs.map f).sum) hmap
  obtain ⟨hcount,hparams,hN,hcoords,hspan,htargets,hvolume⟩ := selectedCoreClassRawRecovery_profile ct h i
    u target width L hu htarget hw hwidth hguard hcell hprepare α gap C V bounds Fs hF
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_ofFn] using hcount
  · intro r hr
    exact hparams r.rawRecoveryJob (by rw [←hmap]; exact List.mem_map.mpr ⟨r,hr,rfl⟩)
  · intro r hr
    exact hN r.rawRecoveryJob (by rw [←hmap]; exact List.mem_map.mpr ⟨r,hr,rfl⟩)
  · exact (hsum (fun r => replicaHaloLocalCoordinates r.problem)).trans_le hcoords
  · exact (hsum (fun r => r.problem.span)).trans_le hspan
  · intro r hr
    exact htargets r.rawRecoveryJob (by rw [←hmap]; exact List.mem_map.mpr ⟨r,hr,rfl⟩)
  · exact (hsum (fun r => replicaRecoveryLocalVolume r.problem)).trans_le hvolume
  · intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    refine ⟨rfl,?_⟩
    exact selectedComputedCoreSetup_profile ct h i (jobs j) rfl rfl rfl hu htarget rfl rfl

end IntegerMultBounds.MathlibTM2.Cost
