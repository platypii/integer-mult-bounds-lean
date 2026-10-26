module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCoefficientWidth

/-! The shared generated coefficient workspace also covers halo membership arithmetic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem haloLookupWidth_fits (P q w s t u band : ℕ) :
    8*(t+1)^2+2*band+8 < 2^(liftedCoefficientWidth P q w s t u band) := by
  let R := liftedCoefficientSize s t u band
  let N := 2^R
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have htN : t ≤ N := (Nat.lt_size_self t).le.trans
    (Nat.pow_le_pow_right (by decide) (show Nat.size t ≤ R by dsimp [R,liftedCoefficientSize]; omega))
  have hbN : band ≤ N := (Nat.lt_size_self band).le.trans
    (Nat.pow_le_pow_right (by decide) (show Nat.size band ≤ R by dsimp [R,liftedCoefficientSize]; omega))
  have hsq : (t+1)^2 ≤ (2*N)^2 := Nat.pow_le_pow_left (by omega) 2
  have hsmall : 8*(t+1)^2+2*band+8 ≤ 64*N^2 := by nlinarith only [hsq,hbN,hN]
  have hpoly : 64*N^2 = 2^(2*R+6) := by
    dsimp only [N]
    rw [← pow_mul,show R*2 = 2*R by omega,pow_add]
    norm_num
    ring
  apply hsmall.trans_lt
  rw [hpoly]
  apply Nat.pow_lt_pow_right (by decide)
  dsimp [liftedCoefficientWidth,R]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
