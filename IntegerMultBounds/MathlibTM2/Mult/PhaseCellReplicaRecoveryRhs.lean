module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryOwnedFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem

/-! Execute only the recovery RHS construction. The boundary and RHS prefixes
are available for batching; the shared factor and coupling bank survives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 248 Q A U}

def replicaRecoveryRhsCost (H : ReplicaHaloProblem s) :=
  packedBoundaryRecoveryInputsCost H.metadataWidth H.span
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card H.wordWidth+
  preparedSharedLocalFeedCouplingIntervalCost true (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
    H.origin (H.origin+H.span) H.origin H.span H.metadataWidth

noncomputable def replicaRecoveryRhsState (H : ReplicaHaloProblem s) (r : ℕ) (Y : ZMod s → GaussianInt)
    (solutionTail outputTail rhsTail : List (Fin (A+4))) (S : Stacks 248 A) : Stacks 248 A :=
  {S with R := Function.update (Function.update (Function.update (Function.update
    (Function.update S.R 238 solutionTail) 132
      (cstream A H.wordWidth (packedInterval H.origin H.span Y)++outputTail)) 110
      (cstream A H.wordWidth (packedInterval H.origin H.span (replicaRecoveryRhs H r Y))++
        (cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsTail)))
    116 []) 167 []}

theorem replicaRecoveryRhsState_core (H : ReplicaHaloProblem s) (r W : ℕ) (Y : ZMod s → GaussianInt)
    (solutionTail outputTail rhsTail : List (Fin (A+4))) (S : Stacks 248 A)
    (h : ReplicaRecoveryCoreReady H W S) :
    ReplicaRecoveryCoreReady H W (replicaRecoveryRhsState H r Y solutionTail outputTail rhsTail S) := by
  apply ReplicaRecoveryCoreReady.of_owned_frame H W h
    (F := replicaRecoveryRhsState H r Y solutionTail outputTail rhsTail S) rfl
  intro k hk
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  simp [replicaRecoveryRhsState,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2.1,
    hk.2.2.2.2.2.1,hk.2.2.2.2.2.2]

theorem replicaRecoveryRhs_exec (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hsep : H.span+H.band ≤ s) (r W : ℕ)
    (solution : List GaussianInt)
    (hlen : solution.length = (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (hfits : ∀ z ∈ solution, Fits H.wordWidth z)
    (solutionTail words outputTail residual rhsTail : List (Fin (A+4)))
    (hwords : words.length = H.span*H.wordWidth) (hresidual : residual.length = H.span*H.wordWidth)
    (v : HS 248 Q A U) (S : Stacks 248 A) (h : ReplicaRecoveryReady H W S)
    (hsrc : S.R 238 = cstream A H.wordWidth solution++solutionTail)
    (houtput : S.R 132 = words++outputTail)
    (hrhs : S.R 110 = residual++
      (cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsTail)) :
    let Y := boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span)) solution
    ∃ v' n, v'.user = v.user ∧ n ≤ replicaRecoveryRhsCost H ∧
      Exec body (packedBoundaryRecoveryRhs hQ) (mk v S) n
        (mk v' (replicaRecoveryRhsState H r Y solutionTail outputTail rhsTail S)) := by
  have hword : H.wordWidth = 2*H.precision+8 := by
    unfold ReplicaHaloProblem.wordWidth ReplicaHaloProblem.precision executionWidth executionPrecision
    omega
  have hsize := weightWorkspaceWidth_packed_fits (P := 2^15*H.p) (q := H.precision) (w := H.wordWidth)
    (by have hh := H.p_pos; omega) (NeZero.pos s) H.s_lt_t H.u_pos H.band_fit
    (Nat.le_add_right H.origin H.span) H.span_fit
  have hN : S.R 165 = binSyms H.metadataWidth H.span := by
    simpa [embStk,packedRecoveryRuntimeReg,couplingIntervalValue] using h.geometry.encoded 165 (by decide)
  have hspan : H.span < 2^H.metadataWidth := by
    have hh := hsize.2.2.2.1
    exact lt_of_le_of_lt (Nat.le_add_left H.span H.origin) hh
  have he := packedBoundaryRecoveryRhs_exec (body := body) (origin := H.origin) (N := H.span)
    hQ H.s_lt_t hA H.metadataWidth H.band H.origin
    (H.origin+H.span) (2^15*H.p) H.precision H.wordWidth W hspan H.span_fit H.span_fit
    (by
      intro i hi
      exact (mem_haloVertices H.origin (H.origin+H.span) i).mp (Finset.mem_sdiff.mp hi).1)
    solution hlen (H.Fs.reverse.getD r (fun _ => 0)) hfits solutionTail words outputTail hwords v S
    h.bank.workspace h.bank.ready h.rhs h.count hsrc hN h.mask houtput residual rhsTail hresidual hrhs
    h.freshLeft h.freshRight h.masters h.native
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact h.clean _ (by decide))
    (by omega) (by omega) rfl rfl hsep (by have hh := H.span_fit; omega) H.band_fit h.rows h.page h.pageCount
    (by intro j hj; exact H.coupling_coefficients (H.origin+j)) H.coupling_geometry.2
    H.coupling_geometry.1 h.geometry
  exact he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
