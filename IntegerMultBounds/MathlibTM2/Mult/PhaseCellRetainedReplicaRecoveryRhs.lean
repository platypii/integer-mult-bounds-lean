module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareReversedReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingReady

/-! Load reversed original RHS rows directly into the retained coupling input.
The gather queue, scalar counters and coefficient workspace remain reusable. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem prepareRetainedReplicaRecoveryRhs_exec_within (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (placement : ReplicaCouplingPlacement plan)
    (buffers : ReplicaLoopBuffers A) (raw : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaRecoveryRhsHeaders H plan.gather buffers S)
    (ready : RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) raw (embStk weightCacheCoreReg (embStk plan.solver S)))
    (depth : ℕ) :
    let F := {S with R := (Function.update S.R (placement.bank 93)
      (H.Fs.reverse.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R (placement.bank 93)))}
    ∃ vf m, vf.user = v.user ∧ m ≤ reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)) depth
        (prepareReversedReplicaRecoveryRhs plan (placement.bank 93)) (mk v S) m (mk vf F) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers F ∧
      RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) raw (embStk weightCacheCoreReg (embStk plan.solver F)) := by
  dsimp only
  obtain ⟨vf,m,hu,hm,he,hheaders⟩ := prepareReversedReplicaRecoveryRhs_exec_within (body := body)
    H plan (placement.bank 93) (fun k => (placement.bank_gather_disjoint 93 k).symm)
    buffers v S headers depth
  refine ⟨vf,m,hu,hm,he,hheaders,?_⟩
  apply ready.of_frame (S' := embStk weightCacheCoreReg (embStk plan.solver
    {S with R := (Function.update S.R (placement.bank 93)
      (H.Fs.reverse.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R (placement.bank 93)))})) rfl
  intro k hk93 _ _
  have hoff : plan.solver (weightCacheCoreReg k) ≠ placement.bank 93 := by
    rw [← placement.bank_native k]
    intro heq
    have hi := placement.bank_injective heq
    have hv := congrArg (fun i : Fin 168 => i.val) hi
    apply hk93
    apply Fin.ext
    change k.val = 93 at hv ⊢
    exact hv
  exact Function.update_of_ne hoff _ _

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
