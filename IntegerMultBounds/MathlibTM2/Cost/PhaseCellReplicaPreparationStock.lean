module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPreparationStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedReplicaInteriorFast

/-! Simultaneous stock of actual replica preparation is linear in copied cell
rows and packed halos. Binary control work is a shared allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- The repeated allowance has no numerical fast-time factor. -/
theorem replicaPreparationStockCost_le (N B V span L w : ℕ)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hw : 1 ≤ w) :
    3*(prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B) ≤
      3*(preparedOriginAdvanceCost V span w B+2*(span*w)+2*B+10)+
        1500*(B*L*w)+1800*N*(B*L*w+span*w+1) := by
  have hc := prepareReplicaInteriorCacheCost_le N B L w hB hL hw
  have hg := sharedPackedReplicaGatherCost_le V N span L w B hB hL hw
  have hvol : B*L*w ≤ B*L*w+span*w+1 := by omega
  have hrepeat := Nat.mul_le_mul_left N hvol
  nlinarith only [hc,hg,hrepeat]

/-- Reprice the actual trace, with all spectator storage in the initial stock. -/
theorem gatheredReplicaInteriorPreparation_within_linear {T Q A : ℕ} {P U : Type}
    {body : P → Pr P T Q A U} (plan : ReplicaInteriorPlacement T)
    {N B V span L w steps : ℕ} {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (gatheredReplicaInteriorPreparation plan) z steps z')
    (hn : steps ≤ prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hw : 1 ≤ w) (depth : ℕ) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      (3*(preparedOriginAdvanceCost V span w B+2*(span*w)+2*B+10)+
        1500*(B*L*w)+1800*N*(B*L*w+span*w+1))) depth
      (gatheredReplicaInteriorPreparation plan) z steps z' := by
  apply (gatheredReplicaInteriorPreparation_within plan he hn depth).mono
  intro d state hs
  have hb := replicaPreparationStockCost_le N B V span L w hB hL hw
  omega

end IntegerMultBounds.MathlibTM2.Cost
