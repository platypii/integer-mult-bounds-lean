module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryBatchFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInteriorExec

/-! The executed second pass pays the existing shared interior setup once.
Archive reordering and real projection add only linear row traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ} [NeZero s]

theorem replicaRecoveryInteriorTime_affine (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X) htarget :
    replicaRecoveryInteriorTime H (B.problem htarget) = initializedReplicaHaloTime (B.problem htarget)+
      H.Fs.length*(28*(H.span*H.wordWidth)+28)+18 := by
  obtain ⟨_,_,hw,_⟩ := B.problem_sizing htarget
  have hc : (B.problem htarget).Fs.length = H.Fs.length := B.inputs_length
  change reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+initializedReplicaHaloTime (B.problem htarget)+
    realReplicaRowsCost (B.problem htarget).Fs.length (H.span*(B.problem htarget).wordWidth) = _
  rw [hc,hw]
  unfold reverseCopyRowsCost realReplicaRowsCost
  ring

theorem replicaRecoveryInterior_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (replicaRecoveryInteriorTime H (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+H.Fs.length*(38*(H.span*H.wordWidth)+37)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+18 : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := replicaRecoveryBatchInterior_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring
  have hh := hfast H target X B htarget hl hw hr hV hgap hring
  rw [replicaRecoveryInteriorTime_affine H target X B htarget]
  push_cast at hh ⊢
  nlinarith only [hh]

/-- Interior recovery depends on layout, not on how its RHS or target was
constructed. In particular this covers a joint cyclic boundary target. -/
theorem replicaRecoveryInteriorTime_layout_affine (H J : ReplicaHaloProblem s)
    (layout : H.SameLayout J) :
    replicaRecoveryInteriorTime H J = initializedReplicaHaloTime J+
      H.Fs.length*(28*(H.span*H.wordWidth)+28)+18 := by
  change reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+initializedReplicaHaloTime J+
    realReplicaRowsCost J.Fs.length (J.span*J.wordWidth) = _
  rw [layout.count,layout.span,layout.wordWidth]
  unfold reverseCopyRowsCost realReplicaRowsCost
  ring

theorem replicaRecoveryInterior_layout_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H J : ReplicaHaloProblem s),
      H.SameLayout J → H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p →
      2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (replicaRecoveryInteriorTime H J : ℝ) ≤
        (initializedReplicaHaloSharedTime J+H.Fs.length*(38*(H.span*H.wordWidth)+37)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+18 : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := initializedReplicaHalo_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro s _ H J layout hl hw hr hV hgap hring
  have hlJ : J.l ≤ cl*J.p := by simpa only [layout.l,layout.p] using hl
  have hwJ : J.wordWidth ≤ cw*J.p := by simpa only [layout.wordWidth,layout.p] using hw
  have hrJ : 2^J.l ≤ cr*J.p := by simpa only [layout.l,layout.p] using hr
  have hVJ : J.metadataWidth ≤ cV*J.p := by simpa only [layout.metadataWidth,layout.p] using hV
  have hh := hfast J hlJ hwJ hrJ hVJ (by simpa only [layout.t] using hgap)
    (by simpa only [layout.l,layout.t] using hring)
  have hcoords : replicaHaloLocalCoordinates J = replicaHaloLocalCoordinates H := by
    simp only [replicaHaloLocalCoordinates,layout.t,layout.band,layout.origin,layout.span]
  rw [layout.count,layout.span,layout.wordWidth,layout.t,layout.band,layout.origin,
    hcoords,layout.p] at hh
  rw [replicaRecoveryInteriorTime_layout_affine H J layout]
  push_cast at hh ⊢
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Cost
