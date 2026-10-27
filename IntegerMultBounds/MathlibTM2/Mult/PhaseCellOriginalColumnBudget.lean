module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSchurColumnBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitialErrorBudget

/-! The shared executed precision already pays original-column generation error. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

theorem originalColumn_precision (p u l entryBits rhsExp : ℕ) :
    schurColumnBits p entryBits+couplingCountExponent p u+2 ≤
      executionPrecision p l (initialSchurTarget p u entryBits rhsExp) rhsExp := by
  have hs : Nat.size (1+16*p) ≤ 1+16*p := Nat.size_le.mpr (Nat.lt_two_pow_self (n := 1+16*p))
  have hfirst : initialSchurTarget p u entryBits rhsExp =
      recoveryTarget p entryBits+couplingCountExponent p u+16*p+3 := by
    exact recoveryFirstTarget_canonical p (recoveryTarget p entryBits) rhsExp (couplingCountExponent p u)
  rw [hfirst]
  dsimp [schurColumnBits,executionPrecision,executionExponent,inputExponent,sourceExponent,recoveryTarget,recoveryGuardBits]
  omega

theorem originalColumn_width (p u l target rhsExp : ℕ) :
    executionPrecision p l target rhsExp+couplingRowExponent 0 0 (8*p+1) (couplingCountExponent p u)+2 ≤
      executionWidth p l target rhsExp := by
  have hc := couplingCountExponent_le p u
  dsimp [executionPrecision,executionWidth,executionExponent,inputExponent,sourceExponent,couplingRowExponent]
  omega

theorem originalColumn_error_budget (p u l entryBits rhsExp : ℕ) :
    3*(2*PhaseCellBand.width p u+1)*
        (1/(2 : ℝ)^executionPrecision p l (initialSchurTarget p u entryBits rhsExp) rhsExp) ≤
      1/(2 : ℝ)^schurColumnBits p entryBits := by
  have hh := couplingRoundoff_budget (inputExp := 0) (couplingCountExponent_spec p u)
    (originalColumn_precision p u l entryBits rhsExp)
  calc
    _ = ((2*PhaseCellBand.width p u+1 : ℕ) : ℝ)*
        (2/(2 : ℝ)^executionPrecision p l (initialSchurTarget p u entryBits rhsExp) rhsExp)+
      ((2*PhaseCellBand.width p u+1 : ℕ) : ℝ)*((2 : ℝ)^0*
        (1/(2 : ℝ)^executionPrecision p l (initialSchurTarget p u entryBits rhsExp) rhsExp)) := by
          push_cast
          ring
    _ ≤ _ := hh

theorem originalColumn_schur_budget (p u l entryBits rhsExp : ℕ) (hp : 0 < p) :
    (1/(2 : ℝ)^(recoveryTarget p entryBits+2))/(8*(p : ℝ))+(1+16*(p : ℝ))*
      (3*(2*PhaseCellBand.width p u+1)*
        (1/(2 : ℝ)^executionPrecision p l (initialSchurTarget p u entryBits rhsExp) rhsExp)) ≤
      1/(2 : ℝ)^entryBits :=
  schurColumn_total_budget p entryBits hp (originalColumn_error_budget p u l entryBits rhsExp)

theorem originalColumn_magnitude_budget (p u l entryBits rhsExp : ℕ) :
    2+3*(2*PhaseCellBand.width p u+1)*
      (1/(2 : ℝ)^executionPrecision p l (initialSchurTarget p u entryBits rhsExp) rhsExp) ≤ (2 : ℝ)^2 := by
  have hh := originalColumn_error_budget p u l entryBits rhsExp
  have hη : 1/(2 : ℝ)^schurColumnBits p entryBits ≤ 1 :=
    div_le_self (by norm_num) (one_le_pow₀ (by norm_num))
  nlinarith only [hh,hη]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
