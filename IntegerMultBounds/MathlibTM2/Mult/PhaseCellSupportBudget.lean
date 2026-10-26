module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing
public import IntegerMultBounds.NLogN.PhaseCellBand

/-! The generated signed-offset count fits the existing working precision automatically. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

def couplingCountExponent (p u : ℕ) : ℕ := Nat.size (2*PhaseCellBand.width p u+1)

theorem couplingCountExponent_spec (p u : ℕ) :
    2*PhaseCellBand.width p u+1 ≤ 2^couplingCountExponent p u :=
  (Nat.lt_size_self _).le

theorem couplingCountExponent_le (p u : ℕ) : couplingCountExponent p u ≤ 8*p+3 := by
  have hroot : Nat.sqrt (16*p/u) ≤ 16*p :=
    (Nat.sqrt_le_self _).trans (Nat.div_le_self _ _)
  have hcount : 2*PhaseCellBand.width p u+1 ≤ 32*p+3 := by
    dsimp [PhaseCellBand.width]
    omega
  have hlinear := Nat.lt_two_pow_self (n := 8*p+1)
  have hpow : 4*2^(8*p+1) = 2^(8*p+3) := by
    rw [show 8*p+3 = (8*p+1)+2 by omega,pow_add]
    norm_num
    ring
  apply Nat.size_le.mpr
  rw [← hpow]
  omega

theorem couplingCountExponent_le_execution (p u l target rhsExp : ℕ) :
    couplingCountExponent p u ≤ executionExponent p l target rhsExp := by
  have hcount := couplingCountExponent_le p u
  dsimp [executionExponent,inputExponent,sourceExponent]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
