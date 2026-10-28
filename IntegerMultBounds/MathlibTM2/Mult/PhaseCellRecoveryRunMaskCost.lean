module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedRecoveryRunMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloRunMaskCost

/-! Coarse compatibility bounds for the generated recovery-mask ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem recoveryWindowMaskCost_eq (W s t B a b : ℕ) :
    recoveryWindowMaskCost W s t B a b =
      2*(s+t+B+a+b)*(4*W+10)+(580*W+538)+576*(W+4)^2+
        6*(recoveryWindowLower false s B a+recoveryWindowUpper false s B b+
          recoveryWindowLower true s B a+recoveryWindowUpper true s B b)+12*s := by
  simp [recoveryWindowMaskCost,applyRecoveryWindowCost,recoveryWindowFromHeadersCost,
    recoveryWindowCountersCost,tblC]
  ring

theorem recoveryWindowMaskCost_le (W s t B a b : ℕ) :
    recoveryWindowMaskCost W s t B a b ≤ 800*(s+t+B+a+b+1)*(W+4)^2 := by
  let H := s+t+B+a+b+1
  let D := (W+4)^2
  let ends := recoveryWindowLower false s B a+recoveryWindowUpper false s B b+
    recoveryWindowLower true s B a+recoveryWindowUpper true s B b
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hs : s ≤ H := by dsimp [H]; omega
  have hsum : s+t+B+a+b ≤ H := by dsimp [H]; omega
  have hends : ends ≤ 3*H := by
    dsimp only [ends]
    simp only [recoveryWindowLower,recoveryWindowUpper,Bool.false_eq_true,↓reduceIte]
    dsimp [H]
    omega
  have hD : 16 ≤ D := by dsimp [D]; nlinarith only [Nat.zero_le W,Nat.zero_le (W^2)]
  have h4 : 4*W+10 ≤ D := by dsimp [D]; nlinarith only [Nat.zero_le W,Nat.zero_le (W^2)]
  have hlinear : 580*W+538 ≤ 100*H*D := by
    have hh : 580*W+538 ≤ 100*D := by dsimp [D]; nlinarith only [Nat.zero_le W,Nat.zero_le (W^2)]
    exact hh.trans (by nlinarith only [Nat.mul_le_mul_left (100*D) hH])
  have htable : 576*D ≤ 576*H*D := by nlinarith only [Nat.mul_le_mul_left (576*D) hH]
  have hload : 2*(s+t+B+a+b)*(4*W+10) ≤ 2*H*D := by gcongr
  have hrest : 6*ends+12*s ≤ 2*H*D := by nlinarith only [hends,hs,Nat.mul_le_mul_left H hD]
  have heq : recoveryWindowMaskCost W s t B a b =
      2*(s+t+B+a+b)*(4*W+10)+(580*W+538)+576*D+6*ends+12*s := by
    exact recoveryWindowMaskCost_eq W s t B a b
  rw [heq]
  change _ ≤ 800*H*D
  nlinarith only [hlinear,htable,hload,hrest]

theorem closedRecoveryRunMaskCost_le (s t B a b : ℕ) :
    closedRecoveryRunMaskCost s t B a b ≤
      5000*(s+t+B+a+b+1)*(publicationGeometryWidth t B+4)^2 := by
  have hbase := closedHaloRunMaskCost_le_sharp s t B a b
  have hw := recoveryWindowMaskCost_le (publicationGeometryWidth t B) s t B a b
  dsimp only [closedRecoveryRunMaskCost]
  nlinarith only [hbase,hw]

theorem closedRecoveryRunMaskCost_halo_le {s t B a b : ℕ}
    (hst : s ≤ t) (hB : B ≤ s) (ha : a ≤ s) (hb : b ≤ s) :
    closedRecoveryRunMaskCost s t B a b ≤ 5000*(5*t+1)*(4*Nat.size t+11)^2 := by
  have hsize : Nat.size B ≤ Nat.size t := Nat.size_le_size (hB.trans hst)
  have hwidth : publicationGeometryWidth t B+4 ≤ 4*Nat.size t+11 := by
    dsimp [publicationGeometryWidth]; omega
  have hcount : s+t+B+a+b+1 ≤ 5*t+1 := by omega
  exact (closedRecoveryRunMaskCost_le s t B a b).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 5000 hcount) (Nat.pow_le_pow_left hwidth 2))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
