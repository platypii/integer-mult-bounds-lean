module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFirstReplicaPassShared
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRetainedCouplingFast

/-! Price first-pass residual coupling with the existing active-row arithmetic
estimate. Shared setup and native tape traffic remain explicit and paid once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ} [NeZero s]

def replicaCouplingArithmeticTime (H : ReplicaHaloProblem s) : ℕ :=
  retainedPageSpatialIntervalLoopCost false H.precision H.wordWidth s H.t H.band
    H.origin (H.origin+H.span) H.origin H.span

def replicaCouplingTransitionNativeTime (H : ReplicaHaloProblem s) (V : ℕ) : ℕ :=
  replicaCouplingTransitionCost H V-replicaCouplingArithmeticTime H

omit [NeZero s] in
theorem replicaCouplingTransitionCost_split (H : ReplicaHaloProblem s) (V : ℕ) :
    replicaCouplingTransitionCost H V = replicaCouplingTransitionNativeTime H V+replicaCouplingArithmeticTime H := by
  unfold replicaCouplingTransitionNativeTime
  apply (Nat.sub_add_cancel ?_).symm
  unfold replicaCouplingTransitionCost replicaLocalCouplingCost replicaCouplingArithmeticTime
  omega

def releasedReplicaCouplingNativeTime (H : ReplicaHaloProblem s) : ℕ :=
  replicaCouplingHeaderCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    initializeReplicaCouplingRuntimeCost H.metadataWidth (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span)+(4*H.Fs.length+6)+H.Fs.length*(replicaCouplingTransitionNativeTime H H.metadataWidth+3)

theorem releasedReplicaCouplingCost_split (H : ReplicaHaloProblem s) :
    releasedReplicaCouplingCost H = releasedReplicaCouplingNativeTime H+H.Fs.length*replicaCouplingArithmeticTime H := by
  unfold releasedReplicaCouplingCost preparedReplicaCouplingCost releasedReplicaCouplingNativeTime
  rw [replicaCouplingTransitionCost_split]
  ring

theorem releasedReplicaCoupling_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s), H.wordWidth ≤ cw*H.p →
      (releasedReplicaCouplingCost H : ℝ) ≤
        (releasedReplicaCouplingNativeTime H+H.Fs.length*(H.span*(20*H.wordWidth+26)+2) : ℕ)+
        C*H.Fs.length*(retainedCouplingActiveRows false s H.t H.band H.origin (H.origin+H.span) H.origin H.span)*
          ((H.band+1 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := retainedPageSpatialIntervalLoopCost_mask_fast_le cw
  refine ⟨C,hC,?_⟩
  intro s _ H hw
  have hwpos : 1 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hc := hfast H.p H.precision H.wordWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
    false H.p_pos hwpos hw
  have hh := mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg H.Fs.length : (0 : ℝ) ≤ H.Fs.length)
  rw [releasedReplicaCouplingCost_split]
  unfold replicaCouplingArithmeticTime
  push_cast at hh ⊢
  nlinarith only [hh]

end IntegerMultBounds.MathlibTM2.Cost
