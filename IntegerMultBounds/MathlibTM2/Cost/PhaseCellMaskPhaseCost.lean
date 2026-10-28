module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedPublicationMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCouplingSourceMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedRecoveryGuardMask

/-! Separate quadratic phase work from linear scalar-header and output work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def maskPhaseBudget (s t B a b : ℕ) : ℕ :=
  let L := publicationGeometryWidth t B+4
  (t-s+1)*L^2+(s+t+B+a+b+1)*L

theorem closedHaloRunMaskCost_phase_le (s t B a b : ℕ) :
    closedHaloRunMaskCost s t B a b ≤ 4000*maskPhaseBudget s t B a b := by
  let W := publicationGeometryWidth t B
  let L := W+4
  let D := L^2
  let H := s+t+B+a+b+1
  let N := t-s+1
  let R := 2*(haloRunIntervals s t B a b).length+1
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hR : R ≤ 3*N := by have := haloRunIntervals_length_le s t B a b; dsimp [R,N]; omega
  have hsum : s+t+B+a+b ≤ H := by dsimp [H]; omega
  have hs : s ≤ H := by dsimp [H]; omega
  have htB : t+B ≤ H := by dsimp [H]; omega
  have hL : 4 ≤ L := by dsimp [L]; omega
  have hLD : L ≤ D := by dsimp [D]; nlinarith only [hL]
  have h8 : 8*W+8 ≤ D := by dsimp [D,L]; nlinarith only [Nat.zero_le W,Nat.zero_le (W^2)]
  have hlinear : 396*W+554 ≤ 500*H*L := by
    have hh : 396*W+554 ≤ 500*L := by dsimp [L]; omega
    exact hh.trans (by nlinarith only [Nat.mul_le_mul_left (500*L) hH])
  have htable : (40*N+13)*(64*D+8*W+8) ≤ 3445*N*D := by
    calc
      _ ≤ (53*N)*(65*D) := by gcongr <;> omega
      _ = _ := by ring
  have hload : 2*(s+t+B+a+b)*(4*W+10) ≤ 8*H*L := by
    calc
      _ ≤ 2*H*(4*L) := by gcongr <;> dsimp [L] <;> omega
      _ = _ := by ring
  have hpairs : R*(2*W+4) ≤ 6*N*D := by
    calc
      _ ≤ (3*N)*(2*D) := by gcongr; dsimp [L] at hLD; omega
      _ = _ := by ring
  have houtput : 10*s ≤ 3*H*L := by nlinarith only [hs,Nat.mul_le_mul_left H hL]
  have hscan : (19*W+22)*(2*N+1) ≤ 57*N*D := by
    calc
      _ ≤ (19*D)*(3*N) := by gcongr <;> dsimp [L] at hLD <;> omega
      _ = _ := by ring
  have hgeometry : 38*(t+B) ≤ 10*H*L := by nlinarith only [htB,Nat.mul_le_mul_left H hL]
  have heq := closedHaloRunMaskCost_eq s t B a b
  change closedHaloRunMaskCost s t B a b =
    (396*W+554)+38*(t+B)+2*(s+t+B+a+b)*(4*W+10)+
      (40*N+13)*(64*D+8*W+8)+R*(2*W+4)+10*s+(19*W+22)*(2*N+1) at heq
  rw [heq]
  change _ ≤ 4000*(N*D+H*L)
  nlinarith only [hlinear,htable,hload,hpairs,houtput,hscan,hgeometry]

theorem recoveryWindowMaskCost_phase_le (W s t B a b : ℕ) :
    recoveryWindowMaskCost W s t B a b ≤
      1000*((W+4)^2+(s+t+B+a+b+1)*(W+4)) := by
  let H := s+t+B+a+b+1
  let L := W+4
  let D := L^2
  let ends := recoveryWindowLower false s B a+recoveryWindowUpper false s B b+
    recoveryWindowLower true s B a+recoveryWindowUpper true s B b
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hL : 4 ≤ L := by dsimp [L]; omega
  have hs : s ≤ H := by dsimp [H]; omega
  have hsum : s+t+B+a+b ≤ H := by dsimp [H]; omega
  have hends : ends ≤ 3*H := by
    dsimp only [ends]
    simp only [recoveryWindowLower,recoveryWindowUpper,Bool.false_eq_true,↓reduceIte]
    dsimp [H]; omega
  have hlinear : 580*W+538 ≤ 600*H*L := by
    have hh : 580*W+538 ≤ 600*L := by dsimp [L]; omega
    exact hh.trans (by nlinarith only [Nat.mul_le_mul_left (600*L) hH])
  have hload : 2*(s+t+B+a+b)*(4*W+10) ≤ 8*H*L := by
    calc
      _ ≤ 2*H*(4*L) := by gcongr <;> dsimp [L] <;> omega
      _ = _ := by ring
  have hrest : 6*ends+12*s ≤ 8*H*L := by nlinarith only [hends,hs,Nat.mul_le_mul_left H hL]
  have heq := recoveryWindowMaskCost_eq W s t B a b
  change recoveryWindowMaskCost W s t B a b =
      2*(s+t+B+a+b)*(4*W+10)+(580*W+538)+576*D+6*ends+12*s at heq
  rw [heq]
  change _ ≤ 1000*(D+H*L)
  nlinarith only [hlinear,hload,hrest]

theorem closedMaskCosts_phase_le (s t B a b : ℕ) :
    closedPublicationMaskCost s t B a b+closedCouplingSourceMaskCost s t B a b+
      closedRecoveryGuardMaskCost s t B a b ≤ 15000*maskPhaseBudget s t B a b := by
  have hbase := closedHaloRunMaskCost_phase_le s t B a b
  have hw := recoveryWindowMaskCost_phase_le (publicationGeometryWidth t B) s t B a b
  let H := s+t+B+a+b+1
  let L := publicationGeometryWidth t B+4
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hL : 4 ≤ L := by dsimp [L]; omega
  have hwindow : windowMaskCost s a b ≤ 100*H*L := by
    have hh : windowMaskCost s a b ≤ 14*H+14 := by dsimp [windowMaskCost,H]; omega
    nlinarith only [hh,hH,Nat.mul_le_mul_left H hL]
  have hphase : L^2 ≤ (t-s+1)*L^2 := Nat.le_mul_of_pos_left _ (by omega)
  change closedHaloRunMaskCost s t B a b ≤ 4000*((t-s+1)*L^2+H*L) at hbase
  change recoveryWindowMaskCost (publicationGeometryWidth t B) s t B a b ≤ 1000*(L^2+H*L) at hw
  change closedHaloRunMaskCost s t B a b+(closedHaloRunMaskCost s t B a b+windowMaskCost s a b)+
    (closedHaloRunMaskCost s t B a b+recoveryWindowMaskCost (publicationGeometryWidth t B) s t B a b) ≤
      15000*((t-s+1)*L^2+H*L)
  nlinarith only [hbase,hw,hwindow,hphase]

end IntegerMultBounds.MathlibTM2.Cost
