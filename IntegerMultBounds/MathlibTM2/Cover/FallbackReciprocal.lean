module

public import IntegerMultBounds.MathlibTM2.Cover.Itinerary
import Mathlib.FieldTheory.Finite.Basic

/-! Pivot reciprocals modulo a prime power, with one fixed powering step per digit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback

/-- For a modulus of width w+1, iterate w times. All products may be evaluated
in the final ring, so intermediate precision changes require no tape conversions. -/
def pivotReciprocal {R : Type*} [CommMonoid R] (p : ℕ) (x : R) : ℕ → R
  | 0 => x^(p-2)
  | w+1 => let y := pivotReciprocal p x w
    y * (x*y)^(p-1)

theorem mul_pivotReciprocal {R : Type*} [CommMonoid R] (p : ℕ) (hp : 2 ≤ p) (x : R) (w : ℕ) :
    x * pivotReciprocal p x w = x^(p^w*(p-1)) := by
  induction w with
  | zero =>
    simp only [pivotReciprocal,pow_zero,one_mul]
    rw [← pow_succ',show p-2+1 = p-1 by omega]
  | succ w ih =>
    rw [pivotReciprocal,← mul_assoc,← pow_succ',show p-1+1 = p by omega,ih,← pow_mul,pow_succ]
    congr 1
    ring

/-- The computed word is the very inverse used by the elimination itinerary. -/
theorem pivotReciprocal_eq {p : ℕ} (hp : p.Prime) (w : ℕ) (x : ZMod (p^(w+1))) (hx : IsUnit x) :
    pivotReciprocal p x w = Ring.inverse x := by
  apply Eq.symm
  apply Itinerary.inverse_unique
  rw [mul_pivotReciprocal p hp.two_le,← Nat.totient_prime_pow_succ hp]
  obtain ⟨u,rfl⟩ := hx
  simpa only [Units.val_pow_eq_pow_val,Units.val_one] using congrArg Units.val (ZMod.pow_totient u)

end IntegerMultBounds.MathlibTM2.Cover.Fallback
