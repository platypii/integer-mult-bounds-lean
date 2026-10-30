module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedCost
public import IntegerMultBounds.MathlibTM2.StackCallResources

/-! One live numerical iteration uses one replica allowance, including return frames. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedHaloBatchStep_within_stock {Q A : ℕ} {P U : Type}
    {body : P → Pr P 249 Q A U} (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius : ℕ) [NeZero s]
    {v vf : HS 249 Q A U} {S F : Stacks 249 A} {n c : ℕ}
    (he : Exec body (packedHaloBatchStep (P := P) (U := U) (A := A) (Q := Q) hR hQ) (mk v S) n (mk vf F))
    (hn : n ≤ packedFreshOutputCost V (b-a)
      (executionWidth p l (initialSchurTarget p u (boundaryTableBits p boundaryTarget rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)+
      packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V)
    (hp : mnProgPush (packedHaloBatchStep (P := P) (U := U) (A := A) (Q := Q) hR hQ) ≤ c)
    (hb : ∀ f, mnProgPush (body f) ≤ c) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(c+1)*
      packedKeyNormalizedReplicaCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius)
      depth (packedHaloBatchStep (P := P) (U := U) (A := A) (Q := Q) hR hQ) (mk v S) n (mk vf F) := by
  have hcost := hn.trans (packedHaloBatchStepCost_le_normalizedReplicaCost
    p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius)
  apply mn_exec_within he hp hb depth
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (c+1) hcost) _

/-- Reprice the complete numerical loop's single workspace allowance with the
same normalized replica ledger used by the caller's time bound. -/
theorem packedHaloBatch_within_replica_stock {Q A : ℕ} {P U : Type}
    {body : P → Pr P 249 Q A U} (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius : ℕ) [NeZero s]
    {v vf : HS 249 Q A U} {S F : Stacks 249 A} {n c H depth : ℕ}
    (htrace : let w := executionWidth p l (initialSchurTarget p u
      (boundaryTableBits p boundaryTarget rhsExp
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2
      ExecWithin body (fun d z => mnSize z+d ≤ H+depth+(c+1)*
        (packedFreshOutputCost V (b-a) w+packedHaloPreparedInputCost p u l finalTarget rhsExp s t a b V))
        depth (packedHaloBatch hR hQ) (mk v S) n (mk vf F)) :
    ExecWithin body (fun d z => mnSize z+d ≤ H+depth+(c+1)*
      packedKeyNormalizedReplicaCost p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius)
      depth (packedHaloBatch hR hQ) (mk v S) n (mk vf F) := by
  apply htrace.mono
  intro d z hz
  have hc := Nat.mul_le_mul_left (c+1) (packedHaloBatchStepCost_le_normalizedReplicaCost
    p q W u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius)
  exact hz.trans (Nat.add_le_add_left hc _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
