module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceIntervalMaskHost

/-! Exactly the retained controls read by the packed assembly loop. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure ReplicaAssemblyControls {s T A : ℕ} (H : ReplicaHaloProblem s)
    (gather : Fin 126 → Fin T) (master : Fin T) (S : Stacks T A) : Prop where
  mask : S.R master = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin
    (H.origin+H.span) H.origin H.span
  width : (S.R (gather 94)).length = H.wordWidth
  replicas : (S.R (gather 121)).length = H.Fs.length

theorem ReplicaAssemblyControls.transport {s T T' A : ℕ} {H : ReplicaHaloProblem s}
    {gather : Fin 126 → Fin T} {gather' : Fin 126 → Fin T'} {master : Fin T} {master' : Fin T'}
    {S : Stacks T A} {F : Stacks T' A} (h : ReplicaAssemblyControls H gather master S)
    (hm : F.R master' = S.R master) (hw : F.R (gather' 94) = S.R (gather 94))
    (hn : F.R (gather' 121) = S.R (gather 121)) : ReplicaAssemblyControls H gather' master' F :=
  ⟨hm.trans h.mask,(congrArg List.length hw).trans h.width,(congrArg List.length hn).trans h.replicas⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
