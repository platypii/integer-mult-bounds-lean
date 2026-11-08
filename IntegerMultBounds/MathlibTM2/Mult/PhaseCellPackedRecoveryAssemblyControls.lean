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
  kernel : (S.R (gather 114)).length = 2^15*H.p
  precision : (S.R (gather 112)).length = H.precision
  origin : (S.R (gather 111)).length = H.origin
  endpoint : (S.R (gather 113)).length = H.origin+H.span
  volume : (S.R (gather 123)).length = H.span*H.wordWidth

theorem ReplicaAssemblyControls.transport {s T T' A : ℕ} {H : ReplicaHaloProblem s}
    {gather : Fin 126 → Fin T} {gather' : Fin 126 → Fin T'} {master : Fin T} {master' : Fin T'}
    {S : Stacks T A} {F : Stacks T' A} (h : ReplicaAssemblyControls H gather master S)
    (hm : F.R master' = S.R master)
    (hf : ∀ i ∈ ([(94 : Fin 126),121,114,112,111,113,123]), F.R (gather' i) = S.R (gather i)) :
    ReplicaAssemblyControls H gather' master' F :=
  ⟨hm.trans h.mask,(congrArg List.length (hf 94 (by simp))).trans h.width,
    (congrArg List.length (hf 121 (by simp))).trans h.replicas,
    (congrArg List.length (hf 114 (by simp))).trans h.kernel,
    (congrArg List.length (hf 112 (by simp))).trans h.precision,
    (congrArg List.length (hf 111 (by simp))).trans h.origin,
    (congrArg List.length (hf 113 (by simp))).trans h.endpoint,
    (congrArg List.length (hf 123 (by simp))).trans h.volume⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
