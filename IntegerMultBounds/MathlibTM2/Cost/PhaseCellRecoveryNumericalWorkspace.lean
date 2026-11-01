module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualSolveStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial

/-! Polynomial scratch bounds for the numerical workers reused by recovery. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem realWeightWorkspace_poly {C w N Z : ℕ} (hZ : 1 ≤ Z)
    (hC : C ≤ Z) (hw : w ≤ Z) (hN : N ≤ Z) :
    realWeightWorkspace C w N ≤ 1000*(ssMulConst+1)*Z^4 := by
  have hm := band_rmul_le hw hZ
  have hmono : realWeightWorkspace C w N ≤ Z*(288*(ssMulConst+1)*Z^3)+7*(Z*Z)+6 := by
    unfold realWeightWorkspace
    gcongr
  have h2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h0 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have hscale : Z^4 ≤ (ssMulConst+1)*Z^4 := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith only [hmono,h2,h0,hscale]

theorem realScalarWorkspace_poly {C w N Z : ℕ} (hZ : 1 ≤ Z)
    (hC : C ≤ Z) (hw : w ≤ Z) (hN : N ≤ Z) :
    realScalarWorkspace C w N ≤ 1000*(ssMulConst+1)*Z^4 := by
  have hm := band_rmul_le hw hZ
  have hmono : realScalarWorkspace C w N ≤ Z*(288*(ssMulConst+1)*Z^3+2*Z+6)+5*(Z*Z)+4 := by
    unfold realScalarWorkspace
    gcongr
  have h2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have hscale : Z^4 ≤ (ssMulConst+1)*Z^4 := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith only [hmono,h2,h1,h0,hscale]

theorem preparedResidualSolveWorkspace_poly {D E R C q w N W Z : ℕ} (hZ : 1 ≤ Z)
    (hD : D ≤ Z) (hE : E ≤ Z) (hR : R ≤ Z) (hC : C ≤ Z)
    (hq : q ≤ Z) (hw : w ≤ Z) (hN : N ≤ Z) (hW : W ≤ Z) :
    preparedResidualSolveWorkspace D E R C q w N W ≤ 100000*(ssMulConst+1)*Z^4 := by
  have hnorm := realScalarWorkspace_poly hZ hD hw hN
  have hunscale := realScalarWorkspace_poly hZ hE hw hN
  have hcolumn := realWeightWorkspace_poly hZ hC hw hW
  have hreciprocal := realWeightWorkspace_poly hZ hR hw hZ
  have htraffic : 2000*(q+1)+10000*(N+1)*(W+1)*(w+1)+2*(4*N*w+4*W*w+8) ≤
      2000*(Z+1)+10000*(Z+1)*(Z+1)*(Z+1)+2*(4*Z*Z+4*Z*Z+8) := by gcongr
  have h3 : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have hscale : Z^4 ≤ (ssMulConst+1)*Z^4 := Nat.le_mul_of_pos_left _ (by omega)
  unfold preparedResidualSolveWorkspace boundarySolveWorkspace
  nlinarith only [hnorm,hunscale,hcolumn,hreciprocal,htraffic,h3,h2,h1,h0,hscale]

end IntegerMultBounds.MathlibTM2.Cost
