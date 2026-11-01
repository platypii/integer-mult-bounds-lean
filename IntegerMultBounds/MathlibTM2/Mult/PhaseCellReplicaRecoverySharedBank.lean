module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseReplicaCouplingNative

/-! Shared numerical/geometry data needed after coupling. Native arithmetic is
still live here; its paid release supplies the stronger recovery-core language. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

structure ReplicaRecoverySharedBank (H : ReplicaHaloProblem s) (W : ℕ) (S : Stacks 248 A) : Prop where
  bank : PackedPreparedBank H.precision H.wordWidth W
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (embStk packedBoundaryRecoveryBase S)
  headers : PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
    H.origin (H.origin+H.span) H.metadataWidth H.wordWidth (embStk packedRecoveryRuntimeReg S)
  rhs : S.R 143 = []
  privateBank : ∀ k : Fin 248, 242 ≤ k.val → S.L k = [] ∧ S.R k = []
  clean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), S.R k = []
  rows : (S.R 140).length = 2*H.band+1
  page : S.R 138 = cstream A H.wordWidth
    (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)
  pageCount : (S.R 139).length =
    (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length

theorem ReplicaRecoverySharedBank.released (H : ReplicaHaloProblem s) (W : ℕ) (S : Stacks 248 A)
    (h : ReplicaRecoverySharedBank H W S) : ReplicaRecoveryCoreReady H W (releasedReplicaCouplingNative S) :=
  ReplicaRecoveryCoreReady.of_coupling_release H W S h.bank h.headers h.rhs h.privateBank h.clean h.rows h.page h.pageCount

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
