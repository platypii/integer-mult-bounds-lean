module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryResourceBudgets

/-! Exact raw-caller budgets independent of recovery-batch solution witnesses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {U : Type}

/-- All caller work except the second interior pass. Subtraction extracts the
additive context from the existing bill without duplicating its formula. -/
def firstCachedRecoveryOverheadTime (H : ReplicaHaloProblem s) : ℕ :=
  firstCachedReplicaRecoveryTime H H-replicaRecoveryInteriorTime H H

noncomputable def firstCachedRecoveryOverheadWorkspace (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K : ℕ) : ℕ :=
  firstCachedReplicaRecoveryWorkspace H H hQ push c M R K-
    replicaRecoveryInteriorWorkspace (A := A) (U := U) H H hQ R K

theorem firstCachedRecoveryTime_eq_overhead (H J : ReplicaHaloProblem s) :
    firstCachedReplicaRecoveryTime H J = firstCachedRecoveryOverheadTime H+replicaRecoveryInteriorTime H J := by
  unfold firstCachedRecoveryOverheadTime firstCachedReplicaRecoveryTime
    initializedCachedBatchedReplicaRecoveryTime cachedBatchedReplicaRecoveryTime
  omega

theorem firstCachedRecoveryWorkspace_eq_overhead (H J : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (push : BoundarySolvePushBounds (A := A) (U := U) hQ)
    (c M R K : ℕ) :
    firstCachedReplicaRecoveryWorkspace H J hQ push c M R K =
      firstCachedRecoveryOverheadWorkspace H hQ push c M R K+
        replicaRecoveryInteriorWorkspace (A := A) (U := U) H J hQ R K := by
  unfold firstCachedRecoveryOverheadWorkspace firstCachedReplicaRecoveryWorkspace
    preparedCachedBatchedReplicaRecoveryWorkspace initializedCachedBatchedReplicaRecoveryWorkspace
    cachedBatchedReplicaRecoveryWorkspace
  omega

namespace RawRecoveryJob

noncomputable def timeBudget (r : RawRecoveryJob s) : ℕ :=
  r.inputTime+generatedReplicaBoundaryFactoryCost r.problem r.target+
    firstCachedRecoveryOverheadTime r.problem+r.problem.recoveryInteriorTimeBudget r.target

noncomputable def stockBudget (r : RawRecoveryJob s) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K : ℕ) : ℕ :=
  r.initialStock (A := A)+normalizeRecoveryInputPush (Q := Q) (A := A) (U := U)*r.inputTime+
    generatedRecoveryInputStock r.problem [] []+
    generatedReplicaBoundaryFactoryPush (A := A) (U := U) hR hQ*
      generatedReplicaBoundaryFactoryCost r.problem r.target+
    firstCachedRecoveryOverheadWorkspace r.problem hQ push c M R K+
    r.problem.recoveryInteriorWorkspaceBudget (A := A) (U := U) r.target hQ R K

theorem runTime_eq_budget (r : RawRecoveryJob s) (B : ReplicaRecoveryBatch r.problem r.target r.solution) :
    r.runTime B = r.timeBudget := by
  unfold runTime timeBudget
  rw [firstCachedRecoveryTime_eq_overhead,recovery_interiorTime_eq_budget r.problem r.target r.solution B r.sizing]
  omega

theorem runStock_eq_budget (r : RawRecoveryJob s) (B : ReplicaRecoveryBatch r.problem r.target r.solution)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K : ℕ) :
    r.runStock hR hQ push c M R K B = r.stockBudget hR hQ push c M R K := by
  unfold runStock stockBudget generatedFirstCachedReplicaRecoveryWorkspace
  rw [firstCachedRecoveryWorkspace_eq_overhead,
    recovery_interiorWorkspace_eq_budget r.problem r.target r.solution B r.sizing]
  omega

/-- The already-proved physical caller supplies a batch witness for every
mathematical raw job. No external solution or execution premise is required. -/
theorem batch_nonempty (r : RawRecoveryJob s) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U)))
    (M : ℕ) (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (v : HS 392 Q A U) :
    Nonempty (ReplicaRecoveryBatch r.problem r.target r.solution) := by
  obtain ⟨B,_⟩ := normalizedGeneratedRecovery_exec_within r.problem r.W r.inputFields r.fields
    r.precision_fit r.format_fit hR hQ hA r.span_fit r.origin_lt R K hpushR hpushK r.padding
    [] [] v 0 r.precision_ge r.width_fit r.target push c hpush M hpushM r.solution r.solves r.sizing
  exact ⟨B⟩

end RawRecoveryJob
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
