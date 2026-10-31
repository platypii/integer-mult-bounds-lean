module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGatheredNumericalStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPublishedReplicaTraffic
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPublishedGatheredReplica

/-! Reprice the actual generated solve/publication stock as shared factories
plus linear local traffic. Numerical multiplication time is never used as stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def generatedPublishedReplicaLinearWorkspace (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp cV : ℕ) :=
  let w := executionWidth p l target rhsExp
  let H := mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))
  H*generateReplicaWeightPageCost 0 (2^15*p) s t u (executionPrecision p l target rhsExp) L w B+
    gatheredInteriorLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV+
    preparedGatheredPublicationWorkspace Q A U 0 V span L w B+
    (2*H+146)*N*(B*(L+2^l)*w+span*w+1)

theorem generatedPublishedGatheredReplicaWorkspace_le_linear (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp cV : ℕ) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    generatedPublishedGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp ≤
      generatedPublishedReplicaLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV := by
  let w := executionWidth p l target rhsExp
  let H := mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))
  let X := B*(L+2^l)*w+span*w+1
  have hg := gatheredInteriorWorkspace_le_linear (A := A) (U := U) hQ
    R K p l N B V span L s t u target rhsExp cV hB hL hV
  have hp := preparedGatheredPublicationWorkspace_le_shared Q A U N V span L w B
  have hX : span*w+1 ≤ X := by dsimp only [X]; omega
  have hpub := Nat.mul_le_mul_left (146*N) hX
  have hfactory := Nat.mul_le_mul_left (2*H*N) (show 1 ≤ X by omega)
  change H*generateReplicaWeightPageCost N (2^15*p) s t u (executionPrecision p l target rhsExp) L w B+
    gatheredInteriorWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp+
    preparedGatheredPublicationWorkspace Q A U N V span L w B ≤
    H*generateReplicaWeightPageCost 0 (2^15*p) s t u (executionPrecision p l target rhsExp) L w B+
    gatheredInteriorLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV+
    preparedGatheredPublicationWorkspace Q A U 0 V span L w B+(2*H+146)*N*X
  rw [generateReplicaWeightPageCost_replicas]
  nlinarith only [hg,hp,hpub,hfactory]

/-- Reprice the certified trace, preserving its endpoint, time and accuracy. -/
theorem generatedPublishedGatheredReplica_within_linear {T : ℕ} {P : Type}
    {body : P → Pr P T Q A U} (plan : ReplicaInteriorPlacement T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {R K p l N B V span L s t u target rhsExp cV steps depth : ℕ}
    {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      generatedPublishedGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp)
      depth (generatedPublishedGatheredReplica plan hR hQ) z steps z')
    (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      generatedPublishedReplicaLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV)
      depth (generatedPublishedGatheredReplica plan hR hQ) z steps z' := by
  apply he.mono
  intro d state hs
  have hb := generatedPublishedGatheredReplicaWorkspace_le_linear (A := A) (U := U) hQ
    R K p l N B V span L s t u target rhsExp cV hB hL hV
  omega

end IntegerMultBounds.MathlibTM2.Cost
