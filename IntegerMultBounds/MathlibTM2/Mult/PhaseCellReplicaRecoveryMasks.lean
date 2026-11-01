module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRibbonMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardIntervalHost

/-! The two geometry streams shared by all recovery replicas in a fixed core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Layer
variable {s A : ℕ} [NeZero s]

structure ReplicaRecoveryMasksReady (H : ReplicaHaloProblem s) (S : Stacks 248 A) : Prop where
  ribbon : S.R 159 = (couplingRibbonFlags (s := s) true H.t H.band H.origin (H.origin+H.span)
    H.origin H.span).map (fun flag => pairSym A flag flag)
  guard : S.R 161 = recoveryGuardIntervalSymbols true A s H.t (2*H.band) H.origin
    (H.origin+H.span) H.origin H.span

theorem ReplicaRecoveryMasksReady.of_frame {H : ReplicaHaloProblem s} {S F : Stacks 248 A}
    (h : ReplicaRecoveryMasksReady H S) (h159 : F.R 159 = S.R 159) (h161 : F.R 161 = S.R 161) :
    ReplicaRecoveryMasksReady H F :=
  ⟨h159.trans h.ribbon,h161.trans h.guard⟩

/-- Both retained streams use linear space in the local interval and halo. -/
theorem ReplicaRecoveryMasksReady.length {H : ReplicaHaloProblem s} {S : Stacks 248 A}
    (h : ReplicaRecoveryMasksReady H S) :
    (S.R 159).length+(S.R 161).length = 2*H.span+2*H.band := by
  rw [h.ribbon,h.guard,List.length_map,recoveryGuardIntervalSymbols_length,
    couplingRibbonFlags_eq_map true H.s_lt_t H.band H.origin (H.origin+H.span)
      H.origin H.span H.span_fit H.band_fit H.span_fit]
  simp only [List.length_map,List.length_range]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
