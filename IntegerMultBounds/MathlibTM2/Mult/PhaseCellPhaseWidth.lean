module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficientWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhaseArguments

/-! The phase comparison fits the same workspace as both numerical branches. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem phaseCoefficientWidth_fits (negative : Bool) (P q w s t u band i d : ℕ)
    (hs : 0 < s) (hi : i < s) (hd : d ≤ band) :
    nearestNatural s t (liftedSource s band i)+liftedTarget negative s band i d <
      2^(liftedCoefficientWidth P q w s t u band) ∧
    nearestNatural s t (liftedTarget negative s band i d)+liftedSource s band i <
      2^(liftedCoefficientWidth P q w s t u band) := by
  let R := liftedCoefficientSize s t u band
  let N := 2^R
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hparam (x : ℕ) (hx : Nat.size x ≤ R) : x ≤ N :=
    (Nat.lt_size_self x).le.trans (Nat.pow_le_pow_right (by decide) hx)
  have hsN : s ≤ N := hparam s (by dsimp [R,liftedCoefficientSize]; omega)
  have htN : t ≤ N := hparam t (by dsimp [R,liftedCoefficientSize]; omega)
  have huN : u ≤ N := hparam u (by dsimp [R,liftedCoefficientSize]; omega)
  have hbN : band ≤ N := hparam band (by dsimp [R,liftedCoefficientSize]; omega)
  obtain ⟨_,hsource,htarget⟩ := lifted_coordinate_bound negative hN hsN hbN (hi.le.trans hsN) hd
  obtain ⟨_,_,hnj,hnk,_,_,_⟩ := lattice_coordinate_bounds hN hsN htN huN hsource htarget
  have hnj' := (Nat.le_mul_of_pos_left (nearestNatural s t (liftedSource s band i)) hs).trans hnj
  have hnk' := (Nat.le_mul_of_pos_left (nearestNatural s t (liftedTarget negative s band i d)) hs).trans hnk
  have h23 : N^2 ≤ N^3 := Nat.pow_le_pow_right hN (by decide)
  have hbase : 32*N^3 < 2^(liftedCoefficientWidth P q w s t u band) := by
    have he : 32*N^3 = 2^(3*R+5) := by
      dsimp only [N]
      rw [← pow_mul,show R*3 = 3*R by omega,pow_add]
      norm_num
      ring
    rw [he]
    apply Nat.pow_lt_pow_right (by decide)
    dsimp [liftedCoefficientWidth,R]
    omega
  constructor <;> apply lt_of_le_of_lt _ hbase <;> omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
