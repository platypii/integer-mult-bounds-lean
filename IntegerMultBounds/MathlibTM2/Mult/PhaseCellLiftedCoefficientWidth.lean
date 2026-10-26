module

public import IntegerMultBounds.NLogN.PhaseCellLatticeBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUnarySize

/-! One logarithmic workspace selection controls all lifted-coordinate and
exponential intermediates. It is shared by every ambient row and band offset. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.NLogN.PhaseCellRationalArgs

def liftedCoefficientSize (s t u band : ℕ) : ℕ :=
  Nat.size s+Nat.size t+Nat.size u+Nat.size band+1

def liftedCoefficientWidth (P q w s t u band : ℕ) : ℕ :=
  w+q+13*P+8*liftedCoefficientSize s t u band+16

structure LiftedCoefficientFits (negative : Bool) (V w q P s t u band i d : ℕ) : Prop where
  coordinates : i+band*s+d < 2^V
  sourceIndex : 2*t*liftedSource s band i+s < 2^V
  targetIndex : 2*t*liftedTarget negative s band i d+s < 2^V
  twiceModulus : 2*s < 2^V
  sourceNearest : s*nearestNatural s t (liftedSource s band i) < 2^V
  targetNearest : s*nearestNatural s t (liftedTarget negative s band i d) < 2^V
  sourceSquare : latticeDistance s t (liftedSource s band i) (liftedTarget negative s band i d)^2 < 2^V
  targetSquare : latticeDistance s t (liftedTarget negative s band i d) (liftedTarget negative s band i d)^2 < 2^V
  modulusSquare : s^2 < 2^V
  semanticWidth : 13*P+8 ≤ V
  exponentWidth : latticeNumerator s t u (liftedSource s band i) (liftedTarget negative s band i d)*2^(5*P+2) < 2^V
  gridWidth : q+P+2 ≤ V
  targetDimension : t < 2^V
  gaussianWidth : u < 2^V
  wordWidth : w ≤ V

theorem liftedCoefficientWidth_fits (negative : Bool) (P q w s t u band i d : ℕ)
    (hi : i < s) (hd : d ≤ band) :
    LiftedCoefficientFits negative (liftedCoefficientWidth P q w s t u band) w q P s t u band i d := by
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
  obtain ⟨hcoord,hsource,htarget⟩ := lifted_coordinate_bound negative hN hsN hbN (hi.le.trans hsN) hd
  obtain ⟨hidxj,hidxk,hnj,hnk,hdj,hdk,hnum⟩ := lattice_coordinate_bounds hN hsN htN huN hsource htarget
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
  have hN7 : N ≤ N^7 := by simpa using Nat.pow_le_pow_right hN (by decide : 1 ≤ 7)
  have hN2 : N^2 ≤ N^7 := Nat.pow_le_pow_right hN (by decide)
  have hN3 : N^3 ≤ N^7 := Nat.pow_le_pow_right hN (by decide)
  have hN6 : N^6 ≤ N^7 := Nat.pow_le_pow_right hN (by decide)
  have h2 : 4*N^2 ≤ 1024*N^7 := by omega
  have h3 : 16*N^3 ≤ 1024*N^7 := by omega
  have h6 : 1024*N^6 ≤ 1024*N^7 := Nat.mul_le_mul_left _ hN6
  refine ⟨hcoord.trans_lt (h2.trans_lt hbase),hidxj.trans_lt (h3.trans_lt hbase),
    hidxk.trans_lt (h3.trans_lt hbase),?_,hnj.trans_lt (h3.trans_lt hbase),
    hnk.trans_lt (h3.trans_lt hbase),hdj.trans_lt (h6.trans_lt hbase),
    hdk.trans_lt (h6.trans_lt hbase),?_,?_,?_,?_,?_,?_,?_⟩
  · exact (show 2*s ≤ 1024*N^7 by omega).trans_lt hbase
  · exact (Nat.pow_le_pow_left hsN 2).trans_lt ((show N^2 ≤ 1024*N^7 by omega).trans_lt hbase)
  · dsimp only [V,liftedCoefficientWidth]; omega
  · calc
      _ ≤ (1024*N^7)*2^(5*P+2) := Nat.mul_le_mul_right _ hnum
      _ = 2^(7*R+10+(5*P+2)) := by rw [hpoly,← pow_add]
      _ < 2^V := by apply Nat.pow_lt_pow_right (by decide); dsimp [V,liftedCoefficientWidth,R]; omega
  · dsimp only [V,liftedCoefficientWidth]; omega
  · exact htN.trans_lt ((show N ≤ 1024*N^7 by omega).trans_lt hbase)
  · exact huN.trans_lt ((show N ≤ 1024*N^7 by omega).trans_lt hbase)
  · dsimp only [V,liftedCoefficientWidth]; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
