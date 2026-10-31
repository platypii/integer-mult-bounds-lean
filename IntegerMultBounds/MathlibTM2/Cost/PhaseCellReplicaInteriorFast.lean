module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedArithmetic

/-! All replica/cell pairs share startup; repeated cached work has a local fast
bound with no ambient-period factor. Weight-page generation is caller-owned. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem cellBill_le (L R M coord cell packet K J E : ℝ)
    (hL : 1 ≤ L) (hR : 0 ≤ R) (hM : 0 ≤ M) (hK : 0 ≤ K) (hJ : 0 ≤ J) (hE : 0 ≤ E)
    (hc : coord ≤ K*M) (hb : cell ≤ J*R*M) (hp : packet ≤ E*M) :
    L*coord+cell+packet ≤ (K+J+E)*(L+R)*M := by
  have hcoord := mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ L)
  have hKR := mul_nonneg (mul_nonneg hK hR) hM
  have hJL := mul_nonneg (mul_nonneg hJ (by linarith : 0 ≤ L)) hM
  have hEL := mul_le_mul_of_nonneg_right hL (mul_nonneg hE hM)
  have hER := mul_nonneg (mul_nonneg hE hR) hM
  nlinarith only [hcoord,hb,hp,hKR,hJL,hEL,hER]

theorem replicaInteriorBatch_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N B L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p →
      2^l ≤ cr*p →
      weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      (cachedBatchFromOriginsCost p l (N*B) L s t u target rhsExp : ℝ) ≤
      (cachedBatchFromOriginsCost p l 0 L s t u target rhsExp : ℝ)+
        D*(N : ℝ)*B*((L : ℝ)+(2^l : ℕ))*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨K,hK,hcoord⟩ := cachedBatchCoordinate_fast_le cl cw
  obtain ⟨J,hJ,hcell⟩ := cachedBatchCell_fast_le cl cw cr
  let E := 12*cV+9
  refine ⟨K+J+E,by positivity,?_⟩
  intro p l N B L s t u target rhsExp hp hL hl hw hr hV
  let V := weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
    (executionWidth p l target rhsExp) t u
  let M := (p : ℝ)^(129/128 : ℝ)
  have hpacket : 12*V+9 ≤ E*p := by dsimp only [E]; nlinarith only [hV,hp]
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpow : (p : ℝ) ≤ M := Real.self_le_rpow_of_one_le hpR (by norm_num)
  have hpacketR : ((12*V+9 : ℕ) : ℝ) ≤ (E : ℝ)*M := by
    calc
      _ ≤ (E : ℝ)*p := by exact_mod_cast hpacket
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg E)
  have hbill := cellBill_le L (2^l : ℕ) M
    (cachedBatchCoordinateCost p l target rhsExp) (cachedBatchCellCost p l target rhsExp)
    (12*V+9 : ℕ) K J E (by exact_mod_cast hL) (Nat.cast_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hK hJ (Nat.cast_nonneg E)
    (hcoord p l target rhsExp hp hl hw) (hcell p l target rhsExp hp hl hw hr) hpacketR
  calc
    _ = (cachedBatchFromOriginsCost p l 0 L s t u target rhsExp : ℝ)+
        (N : ℝ)*B*((L : ℝ)*(cachedBatchCoordinateCost p l target rhsExp : ℝ)+
          (cachedBatchCellCost p l target rhsExp : ℝ)+(12*V+9 : ℕ)) := by
      rw [replicaInteriorBatchCost_eq]
      dsimp only [V]
      push_cast
      ring
    _ ≤ (cachedBatchFromOriginsCost p l 0 L s t u target rhsExp : ℝ)+
        (N : ℝ)*B*((K+J+E)*((L : ℝ)+(2^l : ℕ))*M) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hbill (by positivity))
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
