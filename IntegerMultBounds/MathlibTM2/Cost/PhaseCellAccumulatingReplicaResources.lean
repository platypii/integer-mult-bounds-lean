module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedAccumulatingGatheredReplica
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedPublishedReplicaStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedPublishedReplicaFast

/-! Independent accumulation removes per-class ambient reversal. Exact affine
comparisons reuse the existing complete fast-time and linear-stock ledgers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem publicationCost_accumulation_saving (N V span L w B : ℕ) :
    preparedGatheredPublicationCost N V span L w B =
      accumulatingGatheredPublicationCost N V span L w B+N*(6*(span*w)+7) := by
  unfold preparedGatheredPublicationCost accumulatingGatheredPublicationCost
    routedEncodedPublicationCost retainedEncodedPublicationCost symbolEncodedPublicationCost
  ring

theorem publicationWorkspace_accumulation_saving (N V span L w B : ℕ) :
    preparedGatheredPublicationWorkspace Q A U N V span L w B =
      accumulatingGatheredPublicationWorkspace Q A U N V span L w B+2*N*(6*(span*w)+7) := by
  unfold preparedGatheredPublicationWorkspace accumulatingGatheredPublicationWorkspace
    routedEncodedPublicationCost retainedEncodedPublicationCost symbolEncodedPublicationCost
  ring

theorem generatedAccumulatingGatheredReplicaCost_le_published
    (p l N B V span L s t u target rhsExp : ℕ) :
    generatedAccumulatingGatheredReplicaCost p l N B V span L s t u target rhsExp ≤
      generatedPublishedGatheredReplicaCost p l N B V span L s t u target rhsExp := by
  unfold generatedAccumulatingGatheredReplicaCost generatedPublishedGatheredReplicaCost
  dsimp only
  rw [publicationCost_accumulation_saving]
  omega

theorem generatedAccumulatingGatheredReplicaWorkspace_le_published (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp : ℕ) :
    generatedAccumulatingGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp ≤
      generatedPublishedGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp := by
  unfold generatedAccumulatingGatheredReplicaWorkspace generatedPublishedGatheredReplicaWorkspace
  dsimp only
  rw [publicationWorkspace_accumulation_saving]
  omega

theorem generatedAccumulatingGatheredReplica_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N B V span L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ B → 1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p →
      2^l ≤ cr*p → weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      (generatedAccumulatingGatheredReplicaCost p l N B V span L s t u target rhsExp : ℝ) ≤
      ((generateReplicaWeightPageCost 0 (2^15*p) s t u (executionPrecision p l target rhsExp)
          L (executionWidth p l target rhsExp) B+
        cachedBatchFromOriginsCost p l 0 L s t u target rhsExp+
        accumulatingGatheredPublicationCost 0 V span L (executionWidth p l target rhsExp) B : ℕ) : ℝ)+
        500*B*L*(executionWidth p l target rhsExp)+
        (preparedOriginAdvanceCost V span (executionWidth p l target rhsExp) B+
          2*(span*executionWidth p l target rhsExp)+2*B+10 : ℕ)+
        D*N*((B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1)*(p : ℝ)^(129/128 : ℝ)+19 := by
  obtain ⟨D,hD,hfast⟩ := generatedPublishedGatheredReplica_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV
  have hc := generatedAccumulatingGatheredReplicaCost_le_published p l N B V span L s t u target rhsExp
  have ht := (Nat.cast_le.mpr hc :
    (generatedAccumulatingGatheredReplicaCost p l N B V span L s t u target rhsExp : ℝ) ≤
      generatedPublishedGatheredReplicaCost p l N B V span L s t u target rhsExp).trans
    (hfast p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV)
  simpa only [publicationCost_accumulation_saving,Nat.zero_mul,Nat.add_zero] using ht

/-- The actual accumulating trace inherits the existing linear local stock
bound; this changes neither its execution nor any correctness certificate. -/
theorem generatedAccumulatingGatheredReplica_within_linear {T : ℕ} {P : Type}
    {body : P → Pr P T Q A U} (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {R K p l N B V span L s t u target rhsExp cV steps depth : ℕ}
    {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      generatedAccumulatingGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp)
      depth (generatedAccumulatingGatheredReplica plan dst hR hQ) z steps z')
    (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      generatedPublishedReplicaLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV)
      depth (generatedAccumulatingGatheredReplica plan dst hR hQ) z steps z' := by
  have hb := (generatedAccumulatingGatheredReplicaWorkspace_le_published (A := A) (U := U) hQ
    R K p l N B V span L s t u target rhsExp).trans
    (generatedPublishedGatheredReplicaWorkspace_le_linear (A := A) (U := U) hQ
      R K p l N B V span L s t u target rhsExp cV hB hL hV)
  apply he.mono
  intro d state hs
  omega

end IntegerMultBounds.MathlibTM2.Cost
