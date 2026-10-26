module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientFromHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCoefficientWidth

/-! Ordinary coefficient parameters fit the generated table workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem liftedCoefficientHeaderState_fits (P q w s t u band i d : ℕ)
    (hi : i < s) (hd : d ≤ band) {A : ℕ} :
    ∀ r, (liftedCoefficientHeaderState (A := A) P q s t u band i d).val r <
      2^(liftedCoefficientWidth P q w s t u band) := by
  let V := liftedCoefficientWidth P q w s t u band
  change ∀ r, (liftedCoefficientHeaderState (A := A) P q s t u band i d).val r < 2^V
  have hf : LiftedCoefficientFits false V w q P s t u band i d := liftedCoefficientWidth_fits false P q w s t u band i d hi hd
  have hPV : P < 2^V := (show P ≤ V by have hh := hf.semanticWidth; omega).trans_lt Nat.lt_two_pow_self
  have hqV : q < 2^V := (show q ≤ V by have hh := hf.gridWidth; omega).trans_lt Nat.lt_two_pow_self
  have hsV : s < 2^V := by have hh := hf.twiceModulus; omega
  have htV : t < 2^V := hf.targetDimension
  have huV : u < 2^V := hf.gaussianWidth
  have hiV : i < 2^V := hi.trans hsV
  have hbV : band < 2^V := by
    have hb := Nat.le_mul_of_pos_right band (show 0 < s by omega)
    have hh := hf.coordinates
    omega
  have hdV : d < 2^V := hd.trans_lt hbV
  intro r
  simp only [liftedCoefficientHeaderState,Function.update_apply]
  split_ifs <;> first | assumption | omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
