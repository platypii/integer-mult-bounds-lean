module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedNumericalStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaPreparationStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatheredReplicaInteriorStock

/-! Reprice the complete certified interior trace: shared setup plus linear
local traffic, independent of the numerical multiplication-time allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def gatheredInteriorWorkspace (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp : ℕ) : ℕ :=
  let w := executionWidth p l target rhsExp
  3*(prepareReplicaInteriorCacheCost N B L w+sharedPackedReplicaGatherCost V N span L w B)+
    (2*generatedPrefixHandoffCost (N*B) L w+
      cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l (N*B) L s t u target rhsExp)

noncomputable def gatheredInteriorLinearWorkspace (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp cV : ℕ) : ℕ :=
  let w := executionWidth p l target rhsExp
  cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp+
    3*(preparedOriginAdvanceCost V span w B+2*(span*w)+2*B+10)+1500*(B*L*w)+38+
    (1872+cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV)*
      N*(B*(L+2^l)*w+span*w+1)

private theorem gatheredStockTraffic_le (F N B L r span w : ℕ) :
    1800*N*(B*L*w+span*w+1)+72*N*B*L*w+F*(N*B)*(L+r)*w ≤
      (1872+F)*N*(B*(L+r)*w+span*w+1) := by
  let X := B*(L+r)*w+span*w+1
  have hrow : B*L*w ≤ B*(L+r)*w := by
    exact Nat.mul_le_mul_right w (Nat.mul_le_mul_left B (Nat.le_add_right L r))
  have hprep : B*L*w+span*w+1 ≤ X := by dsimp only [X]; omega
  have hhand : B*L*w ≤ X := by dsimp only [X]; omega
  have hnum : B*(L+r)*w ≤ X := by dsimp only [X]; omega
  have hp := Nat.mul_le_mul_left (1800*N) hprep
  have hh := Nat.mul_le_mul_left (72*N) hhand
  have hn := Nat.mul_le_mul_left (F*N) hnum
  dsimp only [X] at hp hh hn
  nlinarith only [hp,hh,hn]

theorem gatheredInteriorWorkspace_le_linear (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp cV : ℕ) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    gatheredInteriorWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp ≤
      gatheredInteriorLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV := by
  let w := executionWidth p l target rhsExp
  have hw : 1 ≤ w := by dsimp [w,executionWidth]; omega
  have hp := replicaPreparationStockCost_le N B V span L w hB hL hw
  have hh := Nat.mul_le_mul_left 2 (generatedPrefixHandoffCost_le (N*B) L w hL hw)
  have hh' : 2*generatedPrefixHandoffCost (N*B) L w ≤ 72*N*B*L*w+38 := by
    calc
      _ ≤ 2*(36*(N*B)*L*w+19) := hh
      _ = _ := by ring
  have hn := cachedOriginsWorkspace_le_shared_add_traffic (P₀ := Empty) (A := A) (U := U)
    hQ R K p l (N*B) L s t u target rhsExp cV hL hV
  have ht := gatheredStockTraffic_le
    (cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV) N B L (2^l) span w
  unfold gatheredInteriorWorkspace gatheredInteriorLinearWorkspace
  dsimp only
  dsimp only [w] at hp hh' ht
  omega

private theorem gatheredLocalVolume_le (cw cr p B L r span w : ℕ)
    (hw : 1 ≤ w) (hwidth : w ≤ cw*p) (hpad : r ≤ cr*L) :
    B*(L+r)*w+span*w+1 ≤ (cr+1)*cw*(B*L+span+1)*p := by
  have hrow : B*(L+r)*w ≤ (cr+1)*(B*L)*w := by
    have hh := Nat.mul_le_mul_left B hpad
    have hh' := Nat.mul_le_mul_right w hh
    nlinarith only [hh']
  have hspan : span*w ≤ (cr+1)*(span*w) := Nat.le_mul_of_pos_left _ (by omega)
  have hone : 1 ≤ (cr+1)*w := by nlinarith only [hw]
  calc
    _ ≤ (cr+1)*(B*L+span+1)*w := by nlinarith only [hrow,hspan,hone]
    _ ≤ (cr+1)*(B*L+span+1)*(cw*p) := Nat.mul_le_mul_left _ hwidth
    _ = _ := by ring

/-- Tight cell padding turns the repeated allowance into local row volume times precision. -/
theorem gatheredInteriorLinearWorkspace_le_row_volume (hQ : SS.states ≤ Q)
    (R K p l N B V span L s t u target rhsExp cV cw cr : ℕ)
    (hwidth : executionWidth p l target rhsExp ≤ cw*p) (hpad : 2^l ≤ cr*L) :
    gatheredInteriorLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV ≤
      cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp+
        3*(preparedOriginAdvanceCost V span (executionWidth p l target rhsExp) B+
          2*(span*executionWidth p l target rhsExp)+2*B+10)+
        1500*(B*L*executionWidth p l target rhsExp)+38+
        ((1872+cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV)*
          (cr+1)*cw)*N*(B*L+span+1)*p := by
  have hw : 1 ≤ executionWidth p l target rhsExp := by unfold executionWidth; omega
  have hv := gatheredLocalVolume_le cw cr p B L (2^l) span _ hw hwidth hpad
  have hh := Nat.mul_le_mul_left
    ((1872+cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV)*N) hv
  unfold gatheredInteriorLinearWorkspace
  dsimp only
  calc
    _ ≤ _ := Nat.add_le_add_left hh _
    _ = _ := by ring

/-- Apply the comparison to the actual stock certificate without changing its
execution, endpoint, time, numerical error or physical restoration facts. -/
theorem gatheredInterior_within_linear {T : ℕ} {P : Type} {body : P → Pr P T Q A U}
    (plan : ReplicaInteriorPlacement T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {R K p l N B V span L s t u target rhsExp cV steps depth : ℕ}
    {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      gatheredInteriorWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp)
      depth (gatheredReplicaInteriorBatch plan hR hQ) z steps z')
    (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ cV*executionWidth p l target rhsExp) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      gatheredInteriorLinearWorkspace (A := A) (U := U) hQ R K p l N B V span L s t u target rhsExp cV)
      depth (gatheredReplicaInteriorBatch plan hR hQ) z steps z' := by
  apply he.mono
  intro d state hs
  have hb := gatheredInteriorWorkspace_le_linear (A := A) (U := U) hQ
    R K p l N B V span L s t u target rhsExp cV hB hL hV
  omega

end IntegerMultBounds.MathlibTM2.Cost
