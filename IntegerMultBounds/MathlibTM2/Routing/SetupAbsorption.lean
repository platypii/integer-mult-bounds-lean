module

public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! Repeated polynomial dimension setup is eventually paid by record volume.
The concrete routing setup still needs its own polynomial majorant. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open Filter

/-- Uniformly in outer row count and positive payload size, polynomial setup
per row is eventually at most the total physical record volume. -/
theorem repeatedPolynomialSetup_eventually_le_volume (setup : ℕ → ℕ) (A k : ℕ)
    (hsetup : ∀ n, setup n ≤ A * (n + 1) ^ k) :
    ∀ᶠ n : ℕ in atTop, ∀ R B : ℕ, 1 ≤ B → R * setup n ≤ R * 2 ^ n * B := by
  filter_upwards [IntegerMultBounds.MathlibTM2.Mult.Sizes.eventually_mul_pow_le_two_pow (A * 2 ^ k) k,
    eventually_ge_atTop 1] with n hp hn
  intro R B hB
  have hpow := Nat.pow_le_pow_left (by omega : n + 1 ≤ 2 * n) k
  have hs : setup n ≤ 2 ^ n := by
    refine (hsetup n).trans ((Nat.mul_le_mul_left A hpow).trans ?_)
    simpa only [Nat.mul_pow, ← Nat.mul_assoc] using hp
  have hr := Nat.mul_le_mul_left R hs
  have hv : R * 2 ^ n ≤ R * 2 ^ n * B := by
    simpa using Nat.mul_le_mul_left (R * 2 ^ n) hB
  exact hr.trans hv

end IntegerMultBounds.MathlibTM2.Routing
