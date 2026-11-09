module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolvePushBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualBatch
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryNumericalWorkspace

/-! Actual closed-program push counts instantiate the retained solve interface.
The batch adds only linear row storage around one shared arithmetic reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def actualBoundarySolvePushBounds (hQ : SS.states ≤ Q) :
    BoundarySolvePushBounds (A := A) (U := U) hQ where
  normalize := mnProgPush (cmulBlock (rsbCr boundaryFactorReg .vk .dtab .ya) (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) boundaryFactorMulReg boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .vk .dtab .ya)))
  unscale := mnProgPush (cmulBlock (rsbCr boundaryFactorReg .dout .dtab .ya) (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) boundaryFactorMulReg boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .dout .dtab .ya)))
  reciprocal := mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) boundaryFactorMulReg boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .hv .xa .hc))
  column := mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) boundaryFactorMulReg boundaryFactorMulReg_injective (by decide) hQ (rsbCr boundaryFactorReg .ya .xs .pr))
  normalize_push := le_rfl
  unscale_push := le_rfl
  reciprocal_push := le_rfl
  column_push := le_rfl

theorem preparedResidualBatchSolveWorkspace_eq_actual (hQ : SS.states ≤ Q) (q w N W : ℕ) :
    preparedResidualBatchSolveWorkspace (A := A) (U := U) Empty hQ q w N W =
      (actualBoundarySolvePushBounds (A := A) (U := U) hQ).workspace q w N W := by
  rfl

theorem actualResidualBatchWorkspace_eq_shared_add (hQ : SS.states ≤ Q) (q w N W replicas : ℕ) :
    preparedResidualBatchWorkspace (A := A) (U := U) Empty hQ q w N W replicas =
      preparedResidualBatchWorkspace (A := A) (U := U) Empty hQ q w N W 0+replicas*(N*w+12) := by
  unfold preparedResidualBatchWorkspace
  ring

theorem actualResidualBatchWorkspace_zero_poly {hQ : SS.states ≤ Q} {q w N W Z : ℕ}
    (hZ : 1 ≤ Z) (hq : q ≤ Z) (hw : w ≤ Z) (hN : N ≤ Z) (hW : W ≤ Z)
    (hD : (actualBoundarySolvePushBounds (A := A) (U := U) hQ).normalize ≤ Z)
    (hE : (actualBoundarySolvePushBounds (A := A) (U := U) hQ).unscale ≤ Z)
    (hR : (actualBoundarySolvePushBounds (A := A) (U := U) hQ).reciprocal ≤ Z)
    (hC : (actualBoundarySolvePushBounds (A := A) (U := U) hQ).column ≤ Z) :
    preparedResidualBatchWorkspace (A := A) (U := U) Empty hQ q w N W 0 ≤
      200000*(ssMulConst+1)*Z^4 := by
  have hnum := preparedResidualSolveWorkspace_poly hZ hD hE hR hC hq hw hN hW
  have hvol := Nat.mul_le_mul hN hw
  have h₂ : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h₁ : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have h₀ : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have hscale : Z^4 ≤ (ssMulConst+1)*Z^4 := Nat.le_mul_of_pos_left _ (by omega)
  change (actualBoundarySolvePushBounds (A := A) (U := U) hQ).workspace q w N W ≤ _ at hnum
  rw [←preparedResidualBatchSolveWorkspace_eq_actual] at hnum
  unfold preparedResidualBatchWorkspace preparedResidualBatchStepWorkspace
  simp only [Nat.zero_mul,Nat.mul_zero,Nat.zero_add]
  nlinarith only [hnum,hvol,hN,h₂,h₁,h₀,hscale]

end IntegerMultBounds.MathlibTM2.Cost
