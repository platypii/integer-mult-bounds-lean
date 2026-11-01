module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingBounds

/-! Shared physical recovery language. Row-specific solution, RHS and owned
prefixes remain separate from the retained arithmetic and geometry bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

structure ReplicaRecoveryCoreReady (H : ReplicaHaloProblem s) (W : ℕ) (S : Stacks 248 A) : Prop where
  bank : PackedPreparedBank H.precision H.wordWidth W
    (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card (embStk packedBoundaryRecoveryBase S)
  rhs : S.R 143 = []
  freshLeft : ∀ i : Fin 248, 242 ≤ i.val → S.L i = []
  freshRight : ∀ i : Fin 248, 242 ≤ i.val → S.R i = []
  masters : CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)
    (embStk packedRecoveryRuntimeReg S)
  stage : (S.R 118).length = H.stage+1
  level : (S.R 120).length = H.l
  native : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → i ≠ 116 → S.R ⟨i.val,by omega⟩ = []
  clean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), S.R k = []
  rows : (S.R 140).length = 2*H.band+1
  page : S.R 138 = cstream A H.wordWidth
    (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)
  pageCount : (S.R 139).length =
    (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length
  geometry : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span
    (embStk packedRecoveryRuntimeReg S)

/-- Disposable count and mask are seeded from the retained boundary phase. -/
structure ReplicaRecoveryReady (H : ReplicaHaloProblem s) (W : ℕ) (S : Stacks 248 A) : Prop
    extends ReplicaRecoveryCoreReady H W S where
  count : S.R 116 = List.replicate (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card tick
  mask : S.R 167 = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin (H.origin+H.span) H.origin H.span

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
