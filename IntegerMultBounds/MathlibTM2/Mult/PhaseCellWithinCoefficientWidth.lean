module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCoefficientWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficientWord

/-! The same logarithmic workspace also controls the within-cell samples. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellRationalArgs

structure WithinCoefficientFits (V q P s t u j k : ℕ) : Prop where
  sourceIndex : 2*t*j+s < 2^V
  targetIndex : 2*t*k+s < 2^V
  twiceModulus : 2*s < 2^V
  targetDimension : t < 2^V
  modulusSquare : s^2 < 2^V
  weightedSquare : u*s^2 < 2^V
  denominator : similarityDenominator s t < 2^V
  semanticWidth : 13*P+8 ≤ V
  gridWidth : q+2*P+4 ≤ V
  sourceExponent : similarityNumerator s t u j*2^(5*P+2) < 2^V
  targetExponent : similarityNumerator s t u k*2^(5*P+2) < 2^V
  distanceSquare : naturalDistance j k^2 < 2^V
  scaledDistance : t*naturalDistance j k^2 < 2^V
  weightedDistance : u*(t*naturalDistance j k^2) < 2^V
  distanceExponent : (u*t*naturalDistance j k^2)*2^(5*P+2) < 2^V

theorem lifted_naturalDistance (negative : Bool) {s band i d : ℕ}
    (hs : 0 < s) (hd : d ≤ band) :
    naturalDistance (liftedSource s band i) (liftedTarget negative s band i d) = d := by
  have hoff := offset_le_liftedSource (s := s) (band := band) (i := i) hs hd
  dsimp only [liftedSource] at hoff
  cases negative <;> simp [naturalDistance,liftedSource,liftedTarget] <;> omega

theorem withinCoefficientWidth_fits (negative : Bool) (P q w s t u band i d : ℕ)
    (hi : i < s) (hd : d ≤ band) :
    WithinCoefficientFits (liftedCoefficientWidth P q w s t u band) q P s t u
      (liftedSource s band i) (liftedTarget negative s band i d) := by
  let R := liftedCoefficientSize s t u band
  let N := 2^R
  let V := liftedCoefficientWidth P q w s t u band
  have hN : 1 ≤ N := Nat.one_le_two_pow
  have hparam (x : ℕ) (hx : Nat.size x ≤ R) : x ≤ N :=
    (Nat.lt_size_self x).le.trans (Nat.pow_le_pow_right (by decide) hx)
  have hsN : s ≤ N := hparam s (by dsimp [R,liftedCoefficientSize]; omega)
  have htN : t ≤ N := hparam t (by dsimp [R,liftedCoefficientSize]; omega)
  have huN : u ≤ N := hparam u (by dsimp [R,liftedCoefficientSize]; omega)
  have hbN : band ≤ N := hparam band (by dsimp [R,liftedCoefficientSize]; omega)
  have hdN : d ≤ N := hd.trans hbN
  have hdist := lifted_naturalDistance negative (s := s) (i := i) (by omega) hd
  have hpoly : 1024*N^7 = 2^(7*R+10) := by
    dsimp only [N]
    rw [← pow_mul,show R*7 = 7*R by omega,pow_add]
    norm_num
    ring
  have hbase : 1024*N^7 < 2^V := by
    rw [hpoly]
    apply Nat.pow_lt_pow_right (by decide)
    dsimp only [V,liftedCoefficientWidth,R]
    omega
  have hpower (n : ℕ) (hn : n ≤ 7) : N^n ≤ N^7 := Nat.pow_le_pow_right hN hn
  have hsq : s^2 ≤ N^2 := Nat.pow_le_pow_left hsN 2
  have hwsq : u*s^2 ≤ N^3 := by
    calc _ ≤ N*N^2 := Nat.mul_le_mul huN hsq
         _ = N^3 := by ring
  have hden : similarityDenominator s t ≤ 4*N^2 := by
    unfold similarityDenominator
    calc _ ≤ 4*N*N := Nat.mul_le_mul (Nat.mul_le_mul_left 4 hsN) ((Nat.sub_le _ _).trans htN)
         _ = 4*N^2 := by ring
  have hd2 : d^2 ≤ N^2 := Nat.pow_le_pow_left hdN 2
  have htd : t*d^2 ≤ N^3 := by
    calc _ ≤ N*N^2 := Nat.mul_le_mul htN hd2
         _ = N^3 := by ring
  have hud : u*(t*d^2) ≤ N^4 := by
    calc _ ≤ N*N^3 := Nat.mul_le_mul huN htd
         _ = N^4 := by ring
  have hsmall (n : ℕ) (hn : n ≤ 7) : N^n < 2^V :=
    (hpower n hn).trans_lt ((show N^7 ≤ 1024*N^7 by omega).trans_lt hbase)
  have hexp (a : ℕ) (ha : a ≤ N^4) : a*2^(5*P+2) < 2^V := by
    calc _ ≤ (1024*N^7)*2^(5*P+2) := Nat.mul_le_mul_right _
           (ha.trans ((hpower 4 (by decide)).trans (by omega)))
         _ = 2^(7*R+10+(5*P+2)) := by rw [hpoly,← pow_add]
         _ < 2^V := by apply Nat.pow_lt_pow_right (by decide); dsimp [V,liftedCoefficientWidth,R]; omega
  have hfits := liftedCoefficientWidth_fits negative P q w s t u band i d hi hd
  refine ⟨hfits.sourceIndex,hfits.targetIndex,hfits.twiceModulus,hfits.targetDimension,
    hfits.modulusSquare,hwsq.trans_lt (hsmall 3 (by decide)),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hden.trans_lt ((show 4*N^2 ≤ 1024*N^7 by have hh := hpower 2 (by decide); omega).trans_lt hbase)
  · dsimp [V,liftedCoefficientWidth]; omega
  · dsimp [V,liftedCoefficientWidth]; omega
  · exact hexp _ ((similarityNumerator_le _ _ _ _).trans
      (hwsq.trans (Nat.pow_le_pow_right hN (by decide))))
  · exact hexp _ ((similarityNumerator_le _ _ _ _).trans
      (hwsq.trans (Nat.pow_le_pow_right hN (by decide))))
  · rw [hdist]; exact hd2.trans_lt (hsmall 2 (by decide))
  · rw [hdist]; exact htd.trans_lt (hsmall 3 (by decide))
  · rw [hdist]; exact hud.trans_lt (hsmall 4 (by decide))
  · rw [hdist, Nat.mul_assoc u t]; exact hexp _ hud

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
