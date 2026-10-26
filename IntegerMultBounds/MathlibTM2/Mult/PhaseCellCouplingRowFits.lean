module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowError

/-! Derive the coupling accumulator's word allowance from operand magnitudes
and the actual row support. No result-fit or intermediate overflow oracle is needed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem fixedPointRow_sum_norm (q e f : ℕ) (xs as : List GaussianInt)
    (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ)^e)
    (has : ∀ a ∈ as, ‖value q a‖ ≤ (2 : ℝ)^f) :
    ‖value q (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum‖ ≤
      xs.length*(2 : ℝ)^(e+f) := by
  induction xs generalizing as with
  | nil => simp [value_eq_grid]
  | cons x xs ih =>
    cases as with
    | nil => simp at hlen
    | cons a as =>
      have ht := ih as (by simpa using hlen) (fun x hx => hxs x (by simp [hx]))
        (fun a ha => has a (by simp [ha]))
      have hh := normalized_product_norm q 0 e f x a (hxs x (by simp)) (has a (by simp))
      simp only [pow_zero,div_one,Nat.add_zero] at hh
      have hv (z : GaussianInt) (zs : List GaussianInt) :
          value q (z+zs.sum) = value q z+value q zs.sum := by
        apply Complex.ext <;> simp [value,add_div]
      simp only [List.zipWith_cons_cons,List.sum_cons,hv]
      calc
        _ ≤ ‖value q (tdivN q (x*a))‖+
            ‖value q (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum‖ := norm_add_le _ _
        _ ≤ (2 : ℝ)^(e+f)+xs.length*(2 : ℝ)^(e+f) := add_le_add hh ht
        _ = (x::xs).length*(2 : ℝ)^(e+f) := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

def couplingRowExponent (rhsExp inputExp coeffExp countExp : ℕ) : ℕ :=
  max rhsExp (countExp+inputExp+coeffExp)+1

theorem fixedPointRow_norm (q rhsExp inputExp coeffExp countExp : ℕ)
    (rhs : GaussianInt) (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hcount : xs.length ≤ 2^countExp) (hrhs : ‖value q rhs‖ ≤ (2 : ℝ)^rhsExp)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ)^inputExp)
    (has : ∀ a ∈ as, ‖value q a‖ ≤ (2 : ℝ)^coeffExp) :
    ‖value q (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum)‖ ≤
      (2 : ℝ)^couplingRowExponent rhsExp inputExp coeffExp countExp := by
  let e := max rhsExp (countExp+inputExp+coeffExp)
  have hc : (xs.length : ℝ) ≤ (2 : ℝ)^countExp := by exact_mod_cast hcount
  rw [value_sub]
  calc
    _ ≤ ‖value q rhs‖+‖value q (List.zipWith (fun x a => tdivN q (x*a)) xs as).sum‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ)^rhsExp+xs.length*(2 : ℝ)^(inputExp+coeffExp) :=
      add_le_add hrhs (fixedPointRow_sum_norm q inputExp coeffExp xs as hlen hxs has)
    _ ≤ (2 : ℝ)^rhsExp+(2 : ℝ)^countExp*(2 : ℝ)^(inputExp+coeffExp) := by gcongr
    _ ≤ (2 : ℝ)^e+(2 : ℝ)^e := by
      apply add_le_add
      · exact pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
      · rw [← pow_add]
        apply pow_le_pow_right₀ (by norm_num)
        dsimp only [e]; omega
    _ = (2 : ℝ)^couplingRowExponent rhsExp inputExp coeffExp countExp := by
      dsimp only [couplingRowExponent,e]
      rw [pow_succ]; ring

theorem fixedPointRow_fits {q w rhsExp inputExp coeffExp countExp : ℕ}
    (hw : q+couplingRowExponent rhsExp inputExp coeffExp countExp+2 ≤ w)
    (rhs : GaussianInt) (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hcount : xs.length ≤ 2^countExp) (hrhs : ‖value q rhs‖ ≤ (2 : ℝ)^rhsExp)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ)^inputExp)
    (has : ∀ a ∈ as, ‖value q a‖ ≤ (2 : ℝ)^coeffExp) :
    Fits w (rhs-(List.zipWith (fun x a => tdivN q (x*a)) xs as).sum) :=
  fits_of_value_power hw _ (fixedPointRow_norm q rhsExp inputExp coeffExp countExp
    rhs xs as hlen hcount hrhs hxs has)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
