module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerWords

/-! # Dyadic floor encoding by a slice of signed words

The identity is modular and holds for arbitrary signed integers. Signed fits
are needed for decoding the result, not for copying its bit representation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

private theorem emod_mul_ediv (x a b : ℤ) (ha : 0 < a) :
    (x % (a * b)) / a = (x / a) % b := by
  calc
    _ = (x - a * (b * (x / (a * b)))) / a := by rw [Int.emod_def, mul_assoc]
    _ = x / a - b * (x / (a * b)) := Int.sub_mul_ediv_left _ _ ha.ne'
    _ = _ := by rw [Int.ediv_mul_of_nonneg ha.le, Int.emod_def]

theorem residue_mod_pow_two {V W : ℕ} (hV : V ≤ W) (x : ℤ) :
    (x : ZMod (2 ^ W)).val % 2 ^ V = (x : ZMod (2 ^ V)).val := by
  apply Int.ofNat_inj.mp
  push_cast
  rw [val_intCast_eq, val_intCast_eq, Int.emod_emod_of_dvd x (pow_dvd_pow 2 hV)]

theorem residue_div_pow_two (a b : ℕ) (x : ℤ) :
    (x : ZMod (2 ^ (a + b))).val / 2 ^ a = (x / (2 : ℤ) ^ a : ZMod (2 ^ b)).val := by
  apply Int.ofNat_inj.mp
  push_cast
  rw [val_intCast_eq, val_intCast_eq, pow_add, emod_mul_ediv _ _ _ (by positivity)]

theorem residue_testBit {V W : ℕ} (hV : V ≤ W) (x : ℤ) (i : ℕ) (hi : i < V) :
    (x : ZMod (2 ^ W)).val.testBit i = (x : ZMod (2 ^ V)).val.testBit i := by
  have h := congrArg (fun n : ℕ => n.testBit i) (residue_mod_pow_two hV x)
  simpa only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and] using h

theorem csyms_floor_div_append (A a b : ℕ) (z : GaussianInt) :
    csyms A (a + b) z = csyms A a z ++
      csyms A b (⟨z.re / (2 : ℤ) ^ a, z.im / (2 : ℤ) ^ a⟩ : GaussianInt) := by
  simp only [csyms, coeffSyms, red]
  rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext i
    congr 1
    · exact residue_testBit (by omega : a ≤ a + b) z.re i i.isLt
    · exact residue_testBit (by omega : a ≤ a + b) z.im i i.isLt
  · apply congrArg List.ofFn
    funext i
    congr 1
    · rw [← residue_div_pow_two a b z.re]
      simp [Nat.testBit_div_two_pow, Nat.add_comm]
    · rw [← residue_div_pow_two a b z.im]
      simp [Nat.testBit_div_two_pow, Nat.add_comm]

theorem csyms_floor_div_slice (A W a b : ℕ) (hab : a + b ≤ W) (z : GaussianInt) :
    ((csyms A W z).drop a).take b =
      csyms A b (⟨z.re / (2 : ℤ) ^ a, z.im / (2 : ℤ) ^ a⟩ : GaussianInt) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [csyms_floor_div_append A (a + b) c z, csyms_floor_div_append A a b z]
  simp

theorem dyadicWord_ediv {q r : ℕ} (hqr : q ≤ r) (z : ℤ) :
    dyadicWord q r z = (⟨z / (2 : ℤ) ^ (r - q), 0⟩ : GaussianInt) := by
  unfold dyadicWord
  congr 1
  change (2 : ℤ) ^ q * z / (2 : ℤ) ^ r = z / (2 : ℤ) ^ (r - q)
  calc
    _ = (2 : ℤ) ^ q * z / ((2 : ℤ) ^ q * (2 : ℤ) ^ (r - q)) := by
      rw [← pow_add, Nat.add_sub_of_le hqr]
    _ = _ := Int.mul_ediv_mul_of_pos _ _ (by positivity)

theorem csyms_dyadic_slice (A W w q r : ℕ) (hqr : q ≤ r) (hwidth : r - q + w ≤ W) (z : ℤ) :
    ((csyms A W (⟨z, 0⟩ : GaussianInt)).drop (r - q)).take w = csyms A w (dyadicWord q r z) := by
  rw [csyms_floor_div_slice A W (r - q) w hwidth, dyadicWord_ediv hqr]
  simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
