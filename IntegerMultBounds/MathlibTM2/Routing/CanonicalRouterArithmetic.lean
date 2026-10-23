module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStageArithmetic
public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometry

/-! One logarithmic gap and reservoir-compatible stride supply all arithmetic
bounds of every residue profile. The scale is the original record width plus one. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def canonicalRouterGap (n : ℕ) : ℕ := 6 + 4 * Nat.clog 2 (n + 2)

def canonicalRouterStride (n : ℕ) : ℕ := 64 * canonicalRouterGap n

theorem canonicalRouterGap_pos (n : ℕ) : 0 < canonicalRouterGap n := by
  unfold canonicalRouterGap
  omega

theorem canonicalRouter_radix (n : ℕ) : 64 * (n + 1) ^ 4 ≤ 2 ^ canonicalRouterGap n := by
  have hlog : n + 1 ≤ 2 ^ Nat.clog 2 (n + 2) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) (n + 2))
  have hpow := Nat.pow_le_pow_left hlog 4
  have he : 2 ^ canonicalRouterGap n = 64 * (2 ^ Nat.clog 2 (n + 2)) ^ 4 := by
    unfold canonicalRouterGap
    rw [Nat.mul_comm 4 (Nat.clog 2 (n + 2)), pow_add, pow_mul]
    norm_num
  rw [he]
  exact Nat.mul_le_mul_left 64 hpow

theorem canonicalRouter_gap (n : ℕ) :
    1024 * (n + 1) ^ 4 ≤ 2 ^ (canonicalRouterStride n - 1 - canonicalRouterGap n) := by
  have hg : 6 ≤ canonicalRouterGap n := by unfold canonicalRouterGap; omega
  have hexp : canonicalRouterGap n + 4 ≤ canonicalRouterStride n - 1 - canonicalRouterGap n := by
    unfold canonicalRouterStride
    omega
  have hr := Nat.mul_le_mul_left 16 (canonicalRouter_radix n)
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) hexp
  rw [pow_add] at hp
  norm_num at hp
  nlinarith

theorem routerDigits_le_width (n K G : ℕ) : routerDigits n K G ≤ n :=
  (Nat.div_le_self (n - K) (K + 3 * G)).trans (Nat.sub_le n K)

/-- Every numeric fit of a complete canonical input is now constructed for the
actual router residue parameters; no per-profile arithmetic package is assumed. -/
def canonicalRouterArithmetic (n : ℕ) (r : Fin (canonicalRouterStride n))
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) :
    CanonicalStageArithmetic (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val) := by
  apply canonicalStageArithmetic _ (canonicalRouterGap_pos n) ?_ ?_ (n + 1) (by positivity) ?_ ?_ ?_ R B hR hB
  · change 0 < 64 * canonicalRouterGap n
    have := canonicalRouterGap_pos n
    omega
  · change canonicalRouterGap n + 1 < 64 * canonicalRouterGap n
    have := canonicalRouterGap_pos n
    omega
  · change (routerDigits n (canonicalRouterStride n) (canonicalRouterGap n) : ℝ) ≤ (n + 1 : ℕ)
    exact_mod_cast (routerDigits_le_width n (canonicalRouterStride n) (canonicalRouterGap n)).trans (Nat.le_succ n)
  · exact_mod_cast canonicalRouter_radix n
  · exact_mod_cast canonicalRouter_gap n

end
end IntegerMultBounds.MathlibTM2.Routing
