module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryErrorBudget

/-! Allocate the computed boundary matrix and solve errors after the initial RHS allowance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds

def boundaryErrorBits (p target rhsExp : ℕ) : ℕ := target+2*Nat.size (8*p)+rhsExp+5

def boundaryTableBits (p target rhsExp rowCount : ℕ) : ℕ :=
  boundaryErrorBits p target rhsExp+Nat.size rowCount

theorem boundaryTable_error_budget (p target rhsExp rowCount : ℕ) :
    (rowCount : ℝ)*(1/(2 : ℝ)^boundaryTableBits p target rhsExp rowCount) ≤
      1/(2 : ℝ)^boundaryErrorBits p target rhsExp := by
  have hn : (rowCount : ℝ) ≤ (2 : ℝ)^Nat.size rowCount := by exact_mod_cast (Nat.lt_size_self rowCount).le
  rw [mul_one_div]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    _ ≤ (2 : ℝ)^Nat.size rowCount*(2 : ℝ)^boundaryErrorBits p target rhsExp :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by rw [one_mul,← pow_add,boundaryTableBits]; congr 1; omega

theorem boundary_error_budget (p target rhsExp : ℕ) (hp : 0 < p) {εA δ E : ℝ}
    (hεA : 0 ≤ εA) (hδ : 0 ≤ δ)
    (hεbits : εA ≤ 1/(2 : ℝ)^boundaryErrorBits p target rhsExp)
    (hδbits : δ ≤ 1/(2 : ℝ)^boundaryErrorBits p target rhsExp)
    (hE : 8*p*E ≤ 1/(2 : ℝ)^(target+2)) :
    εA < 1/(8*(p : ℝ)) ∧
      (δ+εA*(((2 : ℝ)^rhsExp+δ)/(1/(8*(p : ℝ))-εA))+E)/(1/(8*(p : ℝ))) ≤ 1/(2 : ℝ)^target := by
  let m : ℝ := 8*p
  let h := Nat.size (8*p)
  let r := boundaryErrorBits p target rhsExp
  let η := 1/(2 : ℝ)^r
  let ρ := (2 : ℝ)^rhsExp
  have hm : 0 < m := by dsimp [m]; positivity
  have hmPow : m ≤ (2 : ℝ)^h := by
    dsimp [m,h]
    exact_mod_cast (Nat.lt_size_self (8*p)).le
  have hρ : 1 ≤ ρ := one_le_pow₀ (by norm_num)
  have hη : η ≤ 1/((2 : ℝ)^h*2) := by
    rw [show (2 : ℝ)^h*2 = 2^(h+1) by rw [pow_succ]]
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [r,boundaryErrorBits,h]
    omega
  have hεhalf : εA ≤ (1/m)/2 := by
    apply hεbits.trans (hη.trans ?_)
    rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hmPow]
  have hν : 0 < 1/m-εA := by
    have hpos : 0 < 1/m := by positivity
    linarith
  have hδone : δ ≤ 1 := hδbits.trans ((div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num)))
  have hX : (ρ+δ)/(1/m-εA) ≤ 4*m*ρ := by
    calc
      _ ≤ (ρ+1)/(1/m-εA) := div_le_div_of_nonneg_right (add_le_add le_rfl hδone) hν.le
      _ ≤ (ρ+1)/((1/m)/2) := div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      _ = 2*m*(ρ+1) := by field_simp
      _ ≤ _ := by nlinarith only [hρ,hm.le]
  have hm2 : m^2 ≤ ((2 : ℝ)^h)^2 := pow_le_pow_left₀ hm.le hmPow 2
  have hmLarge : m ≤ (2 : ℝ)^(2*h+rhsExp) := hmPow.trans
    (pow_le_pow_right₀ (by norm_num) (by omega))
  have hprod : m^2*ρ ≤ (2 : ℝ)^(2*h+rhsExp) := by
    calc
      _ ≤ ((2 : ℝ)^h)^2*ρ := mul_le_mul_of_nonneg_right hm2 (by positivity)
      _ = _ := by dsimp [ρ]; rw [← pow_mul,← pow_add]; congr 1; omega
  have hcoeff : m+4*m^2*ρ ≤ (2 : ℝ)^(2*h+rhsExp+3) := by
    rw [pow_add]
    norm_num
    linarith
  have hkernel : m*(δ+εA*((ρ+δ)/(1/m-εA))) ≤ (m+4*m^2*ρ)*η := by
    have hεscaled := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hεbits
      (by positivity : (0 : ℝ) ≤ 4*m*ρ)) hm.le
    have hδscaled := mul_le_mul_of_nonneg_left hδbits hm.le
    have hxscaled := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX hεA) hm.le
    dsimp only [η] at *
    nlinarith only [hεscaled,hδscaled,hxscaled]
  have hquarter : (m+4*m^2*ρ)*η ≤ 1/(2 : ℝ)^(target+2) := by
    apply (mul_le_mul_of_nonneg_right hcoeff (by positivity)).trans
    dsimp only [η]
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul,← pow_add]
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [r,boundaryErrorBits,h]
    omega
  have htotal : m*(δ+εA*((ρ+δ)/(1/m-εA))+E) ≤ 1/(2 : ℝ)^target := by
    have htwo : 4*(1/(2 : ℝ)^(target+2)) = 1/(2 : ℝ)^target := by rw [pow_add]; norm_num; ring
    have hnonneg : 0 ≤ 1/(2 : ℝ)^(target+2) := by positivity
    have hk := hkernel.trans hquarter
    change m*E ≤ _ at hE
    nlinarith only [hk,hE,htwo,hnonneg]
  refine ⟨by change εA < 1/m; linarith [show 0 < 1/m by positivity],?_⟩
  change (δ+εA*((ρ+δ)/(1/m-εA))+E)/(1/m) ≤ _
  simpa only [div_div_eq_mul_div,div_one,mul_comm] using htotal

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
