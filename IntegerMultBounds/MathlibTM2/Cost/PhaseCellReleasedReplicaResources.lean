module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedAccumulatingGatheredReplica
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAccumulatingReplicaResources

/-! Retiring a numerical key adds only linear payload traffic to the complete
class execution. Shared setup and the fast arithmetic exponent are unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def releasedReplicaLinearWorkspace (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp cV : ℕ) :=
  let w := executionWidth p l target rhsExp
  generatedPublishedReplicaLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV+
    96*N*(B*(L+2^l)*w+span*w+1)+60

theorem releasedAccumulatingGatheredReplicaWorkspace_le_linear (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp cV : ℕ) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    releasedAccumulatingGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp ≤
      releasedReplicaLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV := by
  have hc := (generatedAccumulatingGatheredReplicaWorkspace_le_published (A := A) (U := U) hQ
    R K p l N B V span L s t u target rhsExp).trans
    (generatedPublishedGatheredReplicaWorkspace_le_linear (A := A) (U := U) hQ
      R K p l N B V span L s t u target rhsExp cV hB hL hV)
  let w := executionWidth p l target rhsExp
  have hrow : B*L*w ≤ B*(L+2^l)*w+span*w+1 := by
    have hh := Nat.mul_le_mul_right w (Nat.mul_le_mul_left B (Nat.le_add_right L (2^l)))
    omega
  have hh := Nat.mul_le_mul_left (96*N) hrow
  unfold releasedAccumulatingGatheredReplicaWorkspace releasedReplicaLinearWorkspace
  dsimp only
  dsimp only [w] at hh
  nlinarith only [hc,hh]

theorem releasedAccumulatingGatheredReplica_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N B V span L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ B → 1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p →
      2^l ≤ cr*p → weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      (releasedAccumulatingGatheredReplicaCost p l N B V span L s t u target rhsExp : ℝ) ≤
      ((generateReplicaWeightPageCost 0 (2^15*p) s t u (executionPrecision p l target rhsExp)
          L (executionWidth p l target rhsExp) B+
        cachedBatchFromOriginsCost p l 0 L s t u target rhsExp+
        accumulatingGatheredPublicationCost 0 V span L (executionWidth p l target rhsExp) B : ℕ) : ℝ)+
        500*B*L*(executionWidth p l target rhsExp)+
        (preparedOriginAdvanceCost V span (executionWidth p l target rhsExp) B+
          2*(span*executionWidth p l target rhsExp)+2*B+10 : ℕ)+
        D*N*((B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1)*(p : ℝ)^(129/128 : ℝ)+39 := by
  obtain ⟨D,hD,hfast⟩ := generatedAccumulatingGatheredReplica_fast_le cl cw cr cV
  refine ⟨D+32*cw,by positivity,?_⟩
  intro p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV
  let w := executionWidth p l target rhsExp
  let X : ℝ := (B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1
  let M : ℝ := (p : ℝ)^(129/128 : ℝ)
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpM : (p : ℝ) ≤ M := Real.self_le_rpow_of_one_le hpR (by norm_num)
  have hX : (B : ℝ)*L ≤ X := by
    dsimp only [X]
    have hh : (0 : ℝ) ≤ (B : ℝ)*(2^l : ℕ)+span+1 := by positivity
    nlinarith only [hh]
  have hv := Nat.mul_le_mul_left (B*L) hw
  have hvolume : ((B*L*w : ℕ) : ℝ) ≤ cw*X*M := by
    calc
      _ ≤ (B : ℝ)*L*(cw*p) := by exact_mod_cast hv
      _ = cw*((B : ℝ)*L)*p := by ring
      _ ≤ cw*X*p := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX (by positivity)) (by positivity)
      _ ≤ cw*X*M := mul_le_mul_of_nonneg_left hpM (by dsimp only [X]; positivity)
  have ht := mul_le_mul_of_nonneg_left hvolume (show (0 : ℝ) ≤ 32*N by positivity)
  have hc := hfast p l N B V span L s t u target rhsExp hp hB hL hl hw hr hV
  change ((generatedAccumulatingGatheredReplicaCost p l N B V span L s t u target rhsExp+
    (32*((N*B)*L*w)+20) : ℕ) : ℝ) ≤ _
  dsimp only [X,M,w] at ht
  push_cast at hc ht ⊢
  nlinarith only [hc,ht]

theorem releasedAccumulatingGatheredReplica_within_linear {T : ℕ} {P : Type}
    {body : P → Pr P T Q A U} (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {R K p l N B V span L s t u target rhsExp cV steps depth : ℕ}
    {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      releasedAccumulatingGatheredReplicaWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp)
      depth (releasedAccumulatingGatheredReplica plan dst hR hQ) z steps z')
    (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      releasedReplicaLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV)
      depth (releasedAccumulatingGatheredReplica plan dst hR hQ) z steps z' := by
  apply he.mono
  intro d state hs
  have hb := releasedAccumulatingGatheredReplicaWorkspace_le_linear (A := A) (U := U) hQ
    R K p l N B V span L s t u target rhsExp cV hB hL hV
  omega

end IntegerMultBounds.MathlibTM2.Cost
