module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSupportBudget

/-! Allocate guard bits for the complete published recovery error. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN

def recoveryGuardBits (p : ℕ) : ℕ := Nat.size (8*p)+3

def recoveryTarget (p target : ℕ) : ℕ := target+recoveryGuardBits p

theorem couplingRoundoff_budget {n countExp inputExp q target : ℕ}
    (hcount : n ≤ 2^countExp) (hbits : target+countExp+inputExp+2 ≤ q) :
    (n : ℝ)*(2/(2 : ℝ)^q)+(n : ℝ)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q)) ≤ 1/(2 : ℝ)^target := by
  have hn : (n : ℝ) ≤ (2 : ℝ)^countExp := by exact_mod_cast hcount
  have hp : (1 : ℝ) ≤ 2^inputExp := one_le_pow₀ (by norm_num)
  have hnum : (n : ℝ)*(2+(2 : ℝ)^inputExp) ≤ (2 : ℝ)^(countExp+inputExp+2) := by
    calc
      _ ≤ (2 : ℝ)^countExp*(4*(2 : ℝ)^inputExp) :=
        mul_le_mul hn (by linarith) (by positivity) (by positivity)
      _ = _ := by simp only [pow_add]; norm_num; ring
  have hdiv : ((n : ℝ)*(2+(2 : ℝ)^inputExp))/(2 : ℝ)^q ≤ 1/(2 : ℝ)^target := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ (2 : ℝ)^(countExp+inputExp+2)*(2 : ℝ)^target := mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ _ := by
        rw [← pow_add,one_mul]
        apply pow_le_pow_right₀ (by norm_num)
        omega
  convert hdiv using 1
  ring

theorem recoveryGuardBits_spec (p : ℕ) : 1+24*(p : ℝ) ≤ (2 : ℝ)^recoveryGuardBits p := by
  have hp : (8*(p : ℝ)) ≤ (2 : ℝ)^Nat.size (8*p) := by exact_mod_cast (Nat.lt_size_self (8*p)).le
  have hone : (1 : ℝ) ≤ 2^Nat.size (8*p) := one_le_pow₀ (by norm_num)
  rw [recoveryGuardBits,pow_add]
  norm_num
  linarith

theorem recovery_error_budget {p target n countExp inputExp q : ℕ} {ε : ℝ}
    (hcount : n ≤ 2^countExp)
    (hbits : recoveryTarget p target+countExp+inputExp+2 ≤ q)
    (hε : ε ≤ 1/(2 : ℝ)^recoveryTarget p target) :
    max (1/(2 : ℝ)^recoveryTarget p target+8*p*((n : ℝ)*(2/(2 : ℝ)^q)+
      (n : ℝ)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+2*ε)) ε ≤ 1/(2 : ℝ)^target := by
  have hround := couplingRoundoff_budget hcount hbits
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hround
    (mul_le_mul_of_nonneg_left hε (by norm_num : (0 : ℝ) ≤ 2))) (by positivity : (0 : ℝ) ≤ 8*p)
  have hfirst : 1/(2 : ℝ)^recoveryTarget p target+8*p*((n : ℝ)*(2/(2 : ℝ)^q)+
      (n : ℝ)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+2*ε) ≤
      (1+24*(p : ℝ))/(2 : ℝ)^recoveryTarget p target := by
    calc
      _ ≤ 1/(2 : ℝ)^recoveryTarget p target+8*p*(1/(2 : ℝ)^recoveryTarget p target+
          2*(1/(2 : ℝ)^recoveryTarget p target)) := add_le_add le_rfl hscaled
      _ = _ := by ring
  have hamp : (1+24*(p : ℝ))/(2 : ℝ)^recoveryTarget p target ≤ 1/(2 : ℝ)^target := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      _ ≤ (2 : ℝ)^recoveryGuardBits p*(2 : ℝ)^target :=
        mul_le_mul_of_nonneg_right (recoveryGuardBits_spec p) (by positivity)
      _ = _ := by rw [← pow_add,one_mul,recoveryTarget]; congr 1; omega
  apply max_le (hfirst.trans hamp)
  apply hε.trans
  apply one_div_le_one_div_of_le (by positivity)
  apply pow_le_pow_right₀ (by norm_num)
  dsimp [recoveryTarget]
  omega

theorem selected_recovery_error_budget (p u l target rhsExp boundaryExp : ℕ) {ε : ℝ}
    (hε : ε ≤ 1/(2 : ℝ)^recoveryTarget p target) :
    let q := executionPrecision p l
      (recoveryFirstTarget p (recoveryTarget p target) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    max (1/(2 : ℝ)^recoveryTarget p target+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
      (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε)) ε ≤ 1/(2 : ℝ)^target := by
  dsimp only
  let q := executionPrecision p l
    (recoveryFirstTarget p (recoveryTarget p target) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
  have hbits : recoveryTarget p target+couplingCountExponent p u+boundaryExp+2 ≤ q := by
    dsimp only [q]
    rw [(recovery_execution_sizes p l (recoveryTarget p target) rhsExp boundaryExp (couplingCountExponent p u)).1]
    dsimp [executionPrecision,executionExponent,inputExponent,sourceExponent,recoveryRhsExponent,couplingRowExponent]
    omega
  have hh := recovery_error_budget (p := p) (target := target) (q := q)
    (inputExp := boundaryExp) (couplingCountExponent_spec p u) hbits hε
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hh

/-- Extra interior accuracy may be spent independently of the boundary tolerance. -/
theorem recovery_error_budget_of_le {p target workingTarget n countExp inputExp q : ℕ} {ε : ℝ}
    (htarget : recoveryTarget p target ≤ workingTarget)
    (hcount : n ≤ 2^countExp)
    (hbits : recoveryTarget p target+countExp+inputExp+2 ≤ q)
    (hε : ε ≤ 1/(2 : ℝ)^recoveryTarget p target) :
    max (1/(2 : ℝ)^workingTarget+8*p*((n : ℝ)*(2/(2 : ℝ)^q)+
      (n : ℝ)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+2*ε)) ε ≤ 1/(2 : ℝ)^target := by
  have hprecision : 1/(2 : ℝ)^workingTarget ≤ 1/(2 : ℝ)^recoveryTarget p target :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) htarget)
  exact (max_le_max (add_le_add hprecision le_rfl) le_rfl).trans
    (recovery_error_budget hcount hbits hε)

/-- A finer shared arithmetic bank also meets a coarser recovery error target. -/
theorem selected_recovery_error_budget_of_le (p u l target workingTarget rhsExp boundaryExp : ℕ)
    {ε : ℝ} (htarget : target ≤ workingTarget)
    (hε : ε ≤ 1/(2 : ℝ)^recoveryTarget p target) :
    let q := executionPrecision p l
      (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp
    let band := PhaseCellBand.width p u
    max (1/(2 : ℝ)^recoveryTarget p workingTarget+8*p*((2*band+1)*(2/(2 : ℝ)^q)+
      (2*band+1)*((2 : ℝ)^boundaryExp*(1/(2 : ℝ)^q))+2*ε)) ε ≤ 1/(2 : ℝ)^target := by
  dsimp only
  have hbits : recoveryTarget p target+couplingCountExponent p u+boundaryExp+2 ≤
      executionPrecision p l
        (recoveryFirstTarget p (recoveryTarget p workingTarget) rhsExp boundaryExp (couplingCountExponent p u)) rhsExp := by
    rw [(recovery_execution_sizes p l (recoveryTarget p workingTarget) rhsExp boundaryExp (couplingCountExponent p u)).1]
    dsimp [executionPrecision,executionExponent,inputExponent,sourceExponent,recoveryRhsExponent,
      couplingRowExponent,recoveryTarget]
    omega
  have hh := recovery_error_budget_of_le (p := p) (target := target)
    (workingTarget := recoveryTarget p workingTarget) (inputExp := boundaryExp)
    (by dsimp [recoveryTarget]; omega) (couplingCountExponent_spec p u) hbits hε
  simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hh

theorem component_error_budget (target : ℕ) :
    1/(2 : ℝ)^(target+1)+1/(2 : ℝ)^(target+1) = 1/(2 : ℝ)^target := by
  rw [pow_succ]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
