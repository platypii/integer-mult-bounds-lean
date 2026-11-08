module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicRecoveryCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedNativeCyclicBoundaryBatch

/-! The executed projection and preparation endpoints supply the paired batch's
three aligned input queues and boundary-word fit witnesses. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "source" => CyclicRecoveryPlacement.bank 132
variable {s A : ℕ} [NeZero s]

theorem projectedCyclicRecoveryInputs (H K : ReplicaHaloProblem s)
    (t band a n w : ℕ)
    (hHL : H.origin = a) (hHN : H.span = min n (s-a)) (hHW : H.wordWidth = w)
    (hKL : K.origin = 0) (hKN : K.span = n-min n (s-a)) (hKW : K.wordWidth = w)
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hHF : H.Fs = Fs) (hKF : K.Fs = Fs) (hlen : solutions.length = Fs.length)
    (hsolutions : ∀ solution ∈ solutions,
      solution.length = (cyclicPrincipalBoundary s t band a n).card ∧ ∀ z ∈ solution, Fits w z)
    (S : Stacks 840 A) (solveTail : List (Fin (A+4))) :
    let B := cyclicPrincipalBoundary s t band a n
    let rows := cyclicBoundaryRecoveryRows B solutions Fs
    let fields := fun solution => cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
      cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    let G := prepareCyclicRecoveryCouplingState H K
      (placedNativeCyclicBoundaryBatchState S solveTail (solutions.reverse.flatMap fields))
    G.R source = rows.flatMap (fun row => cyclicRecoveryField H row.1++cyclicRecoveryField K row.1)++S.R source ∧
    G.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) = rows.flatMap (fun row => cyclicRecoveryField H row.2.1)++S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) ∧
    G.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) = rows.flatMap (fun row => cyclicRecoveryField K row.2.2)++S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) ∧
    rows.length = Fs.length ∧
    (∀ row ∈ rows, ∀ j, Fits H.wordWidth (row.1 j)) ∧
    (∀ row ∈ rows, ∀ j, Fits K.wordWidth (row.1 j)) := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let fields := fun solution => cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
    cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
  let F := placedNativeCyclicBoundaryBatchState S solveTail (solutions.reverse.flatMap fields)
  have hfield : solutions.reverse.flatMap fields = (cyclicBoundaryRecoveryRows B solutions Fs).flatMap
      (fun row => cyclicRecoveryField H row.1++cyclicRecoveryField K row.1) := by
    rw [cyclicBoundaryRecoveryRows_source H K B solutions Fs hlen]
    simp only [fields,cyclicRecoveryField,hHL,hHN,hHW,hKL,hKN,hKW]
  have hL : F.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) = S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) := by
    simp [F,placedNativeCyclicBoundaryBatchState,
      CyclicRecoveryPlacement.native_left_disjoint 224 _ (.bank 93),
      CyclicRecoveryPlacement.native_left_disjoint 132 _ (.bank 93)]
  have hR : F.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) = S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) := by
    simp [F,placedNativeCyclicBoundaryBatchState,
      CyclicRecoveryPlacement.native_right_disjoint 224 _ (.bank 93),
      CyclicRecoveryPlacement.native_right_disjoint 132 _ (.bank 93)]
  obtain ⟨hstreamL,hstreamR⟩ := cyclicBoundaryRecoveryRows_rhs_streams (A := A) H K B solutions Fs hlen
  obtain ⟨hpreparedL,hpreparedR⟩ := prepareCyclicRecoveryCouplingState_rhs H K F
  refine ⟨?_,?_,?_,cyclicBoundaryRecoveryRows_length B solutions Fs hlen,?_,?_⟩
  · rw [prepareCyclicRecoveryCouplingState_native H K _ 132]
    change F.R source = _
    simp only [F,placedNativeCyclicBoundaryBatchState,
      Function.update_of_ne (CyclicRecoveryPlacement.bank_injective.ne (by decide : (132 : Fin 240) ≠ 224)),
      Function.update_self]
    exact congrArg (fun xs => xs++S.R source) hfield
  · rw [hstreamL]
    change (prepareCyclicRecoveryCouplingState H K F).R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) =
      Fs.reverse.flatMap (fun C => cstream A H.wordWidth (packedInterval H.origin H.span C))++S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93)
    simpa only [hHF,hL] using hpreparedL
  · rw [hstreamR]
    change (prepareCyclicRecoveryCouplingState H K F).R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) =
      Fs.reverse.flatMap (fun C => cstream A K.wordWidth (packedInterval K.origin K.span C))++S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93)
    simpa only [hKF,hR] using hpreparedR
  · simpa only [hHW] using cyclicBoundaryRecoveryRows_fits w B solutions Fs hsolutions
  · simpa only [hKW] using cyclicBoundaryRecoveryRows_fits w B solutions Fs hsolutions

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
