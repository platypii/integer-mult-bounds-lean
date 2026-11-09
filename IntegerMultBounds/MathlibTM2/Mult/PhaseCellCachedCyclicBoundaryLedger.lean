module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicResidualExportLedger
import Mathlib.Tactic.Ring

/-! The complete cached boundary bill has four numerical calls and linear
controller/export traffic. The factor factory remains a single setup charge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem cachedCyclicReplicaBoundaryBill_le_components {s : ℕ} [NeZero s]
    (H K : ReplicaHaloProblem s) (p u l t a n target q w N W replicas : ℕ)
    (hH : H.Fs.length = replicas) (hK : K.Fs.length = replicas)
    (hHW : H.wordWidth = w) (hKW : K.wordWidth = w)
    (hspan : H.span+K.span ≤ n) :
    cachedCyclicReplicaBoundaryBill H K p u l t a n target q w N W replicas ≤
      cachedReplicaPassCost H+cachedReplicaPassCost K+
        (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K)+
        constructedCyclicFactorCost p u l s t a n target 2+
        preparedResidualBatchCost q w N W replicas+
        200*(replicas+1)*(n+N+1)*(w+1) := by
  have he := exportCyclicResidualRowsCost_le replicas n N w
  have hv := Nat.mul_le_mul_right w hspan
  have hr := Nat.mul_le_mul_left replicas hv
  unfold cachedCyclicReplicaBoundaryBill
  rw [hH,hK,hHW,hKW]
  ring_nf at he hv hr ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
