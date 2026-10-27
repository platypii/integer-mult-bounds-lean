module

public import IntegerMultBounds.NLogN.NewtonRecip
public import IntegerMultBounds.BinaryWords
public import Mathlib.Data.Nat.Size

/-! A logarithmic Newton iteration count with a structural contraction proof. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds

def factorNewtonSteps (p q : ℕ) : ℕ := Nat.size (256*p*(q+1))

theorem factorNewtonSteps_bound (p q : ℕ) :
    factorNewtonSteps p q ≤ 8+Nat.size p+Nat.size (q+1) := by
  apply Nat.size_le.mpr
  have hprod : p*(q+1) < 2^Nat.size p*2^Nat.size (q+1) := by
    calc
      _ ≤ 2^Nat.size p*(q+1) := Nat.mul_le_mul_right _ (Nat.lt_size_self p).le
      _ < _ := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self (q+1)) (by positivity)
  calc
    256*p*(q+1) = 256*(p*(q+1)) := by ring
    _ < 256*(2^Nat.size p*2^Nat.size (q+1)) := Nat.mul_lt_mul_of_pos_left hprod (by decide)
    _ = 2^(8+Nat.size p+Nat.size (q+1)) := by simp [pow_add]; ring

private theorem contraction_bound (a : ℝ) (ha : 0 ≤ a) :
    ∀ n : ℕ, (1+(n : ℝ)*(1-a))*a^n ≤ 1
  | 0 => by simp
  | n+1 => by
    have hc : (1+((n : ℝ)+1)*(1-a))*a ≤ 1+(n : ℝ)*(1-a) := by
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n+1) (sq_nonneg (1-a))]
    calc
      _ = ((1+((n : ℝ)+1)*(1-a))*a)*a^n := by push_cast; rw [pow_succ]; ring
      _ ≤ (1+(n : ℝ)*(1-a))*a^n := mul_le_mul_of_nonneg_right hc (pow_nonneg ha n)
      _ ≤ 1 := contraction_bound a ha n

theorem factorNewtonSteps_budget (p q : ℕ) (hp : 0 < p) :
    (1-(1/(32*(p : ℝ)))/4/2)^(2^factorNewtonSteps p q) ≤
      3*(5*(1/(2 : ℝ)^q))/((1/(32*(p : ℝ)))/4) := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  let a : ℝ := 1-1/(256*(p : ℝ))
  have ha : 0 ≤ a := by
    dsimp [a]
    have h : (1 : ℝ)/(256*p) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    have h : (0 : ℝ) ≤ 1/(256*p) := by positivity
    linarith
  have hblock : a^(256*p) ≤ 1/2 := by
    have h := contraction_bound a ha (256*p)
    have he : (1+((256*p : ℕ) : ℝ)*(1-a)) = 2 := by dsimp [a]; push_cast; field_simp; ring
    rw [he] at h
    linarith
  have hexp : 256*p*(q+1) ≤ 2^factorNewtonSteps p q := (Nat.lt_size_self _).le
  have hpow : a^(2^factorNewtonSteps p q) ≤ (1/2 : ℝ)^(q+1) := by
    calc
      _ ≤ a^(256*p*(q+1)) := pow_le_pow_of_le_one ha ha1 hexp
      _ = (a^(256*p))^(q+1) := pow_mul _ _ _
      _ ≤ (1/2 : ℝ)^(q+1) := pow_le_pow_left₀ (pow_nonneg ha _) hblock _
  have haeq : 1-(1/(32*(p : ℝ)))/4/2 = a := by dsimp [a]; ring
  rw [haeq]
  apply hpow.trans
  have hβ : (1 : ℝ)/(32*p) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hconst : (1/2 : ℝ) ≤ 3*5/((1/(32*(p : ℝ)))/4) := by
    apply (le_div_iff₀ (by positivity)).mpr
    linarith only [hβ]
  have h := mul_le_mul_of_nonneg_right hconst (by positivity : (0 : ℝ) ≤ 1/2^q)
  convert h using 1
  · rw [div_pow,pow_succ]; ring
  · ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
