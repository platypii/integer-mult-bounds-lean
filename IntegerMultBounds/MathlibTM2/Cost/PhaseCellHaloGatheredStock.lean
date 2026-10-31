module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloLocalPadding
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGatheredNumericalStock

/-! Aggregate the actual gathered-interior stock envelope over all halo length
classes. Shared charges remain explicit; repeated traffic is local, including
short endpoint cells. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U : Type}

theorem haloGatheredInteriorStock_le_local (hQ : SS.states ≤ Q)
    (R K p N V s t u target rhsExp cV band a b : ℕ) [NeZero s]
    (hst : s < t) (hgap : t-s ≤ s) (hab : a ≤ b) :
    let l := haloInverseRingLog s t
    let w := executionWidth p l target rhsExp
    let count := fun L => (haloLengthGroup s t band a b L).length
    ((haloLengthKeys s t band a b).map (fun L =>
      gatheredInteriorLinearWorkspace (A := A) (U := U) hQ R K p l N (count L) V (b-a) L s t u target rhsExp cV)).sum ≤
      ((haloLengthKeys s t band a b).map (fun L =>
        cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp+
          3*(preparedOriginAdvanceCost V (b-a) w (count L)+2*((b-a)*w)+2*count L+10)+
          1500*(count L*L*w)+38)).sum+
      (1872+cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV)*N*
        (((haloInterior s t band a b).card+8*(b-a)+8*(s/(t-s)+1))*w+6*((b-a)*w+1)) := by
  dsimp only
  let l := haloInverseRingLog s t
  let w := executionWidth p l target rhsExp
  let count := fun L => (haloLengthGroup s t band a b L).length
  let F := 1872+cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV
  have hsplit (xs : List ℕ) :
      (xs.map (fun L => gatheredInteriorLinearWorkspace (A := A) (U := U) hQ
        R K p l N (count L) V (b-a) L s t u target rhsExp cV)).sum =
      (xs.map (fun L => cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ
        R K p l 0 L s t u target rhsExp+
        3*(preparedOriginAdvanceCost V (b-a) w (count L)+2*((b-a)*w)+2*count L+10)+
        1500*(count L*L*w)+38)).sum+
      (xs.map (fun L => (F*N)*(count L*(L+2^l)*w+(b-a)*w+1))).sum := by
    induction xs with
    | nil => simp
    | cons L xs ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [ih]
      simp only [gatheredInteriorLinearWorkspace]
      dsimp only [F,w]
      ring
  rw [hsplit]
  have ht := haloLengthKeys_localTraffic_le hst hgap band a b (F*N) w hab
  exact Nat.add_le_add_left ht _

end IntegerMultBounds.MathlibTM2.Cost
