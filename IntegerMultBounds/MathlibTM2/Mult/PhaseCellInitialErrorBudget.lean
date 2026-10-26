module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryErrorBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds

/-! The shared first-pass target pays its Schur RHS error before the boundary solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

def initialSchurTarget (p u target rhsExp : ℕ) : ℕ :=
  recoveryFirstTarget p (recoveryTarget p target) rhsExp (stableInteriorExponent p rhsExp) (couplingCountExponent p u)

theorem recoveryFirstTarget_canonical (p target rhsExp countExp : ℕ) :
    recoveryFirstTarget p target rhsExp (stableInteriorExponent p rhsExp) countExp =
      target+countExp+16*p+3 := by
  dsimp [recoveryFirstTarget,recoveryRhsExponent,couplingRowExponent,stableInteriorExponent]
  omega

theorem initialResidual_roundoff_budget (p u l target rhsExp : ℕ) :
    let q := executionPrecision p l target rhsExp
    let band := PhaseCellBand.width p u
    (2*band+1)*(2/(2 : ℝ)^q)+(2*band+1)*((2 : ℝ)^stableInteriorExponent p rhsExp*(1/(2 : ℝ)^q)) ≤
      1/(2 : ℝ)^target := by
  dsimp only
  have hbits : target+couplingCountExponent p u+stableInteriorExponent p rhsExp+2 ≤
      executionPrecision p l target rhsExp := by
    have hc := couplingCountExponent_le p u
    dsimp [executionPrecision,executionExponent,inputExponent,sourceExponent,stableInteriorExponent]
    omega
  have hh := couplingRoundoff_budget (couplingCountExponent_spec p u) hbits
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hh

theorem initialResidual_error_budget (p u l target rhsExp : ℕ) (hp : 0 < p) :
    let firstTarget := initialSchurTarget p u target rhsExp
    let q := executionPrecision p l firstTarget rhsExp
    let band := PhaseCellBand.width p u
    8*p*((2*band+1)*(2/(2 : ℝ)^q)+
      (2*band+1)*((2 : ℝ)^stableInteriorExponent p rhsExp*(1/(2 : ℝ)^q))+2*(1/(2 : ℝ)^firstTarget)) ≤
        1/(2 : ℝ)^(recoveryTarget p target+2) := by
  dsimp only
  let T := initialSchurTarget p u target rhsExp
  have hround := initialResidual_roundoff_budget p u l T rhsExp
  have hscaled := mul_le_mul_of_nonneg_left
    (add_le_add hround (le_rfl : 2*(1/(2 : ℝ)^T) ≤ 2*(1/(2 : ℝ)^T))) (by positivity : (0 : ℝ) ≤ 8*p)
  have hres : 8*p*((2*PhaseCellBand.width p u+1)*(2/(2 : ℝ)^executionPrecision p l T rhsExp)+
      (2*PhaseCellBand.width p u+1)*((2 : ℝ)^stableInteriorExponent p rhsExp*
        (1/(2 : ℝ)^executionPrecision p l T rhsExp))+2*(1/(2 : ℝ)^T)) ≤ 24*p/(2 : ℝ)^T := by
    calc
      _ ≤ 8*p*(1/(2 : ℝ)^T+2*(1/(2 : ℝ)^T)) := hscaled
      _ = _ := by ring
  have hpPow : (8*(p : ℝ)) ≤ (2 : ℝ)^(8*p) := by exact_mod_cast (Nat.lt_two_pow_self (n := 8*p)).le
  have hcoeff : 24*(p : ℝ) ≤ (2 : ℝ)^(couplingCountExponent p u+16*p+1) := by
    calc
      _ ≤ 4*(2 : ℝ)^(8*p) := by linarith
      _ = (2 : ℝ)^(8*p+2) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
  apply hres.trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ (2 : ℝ)^(couplingCountExponent p u+16*p+1)*(2 : ℝ)^(recoveryTarget p target+2) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by
      rw [one_mul,← pow_add]
      congr 1
      dsimp only [T,initialSchurTarget]
      rw [recoveryFirstTarget_canonical]
      omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
