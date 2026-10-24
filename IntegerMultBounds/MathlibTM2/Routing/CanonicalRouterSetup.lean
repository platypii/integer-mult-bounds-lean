module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterAmortized

/-! Long records beyond a fixed supplier-dependent dimension pay shared-bank setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

noncomputable def canonicalRouterSetupThreshold : ℕ := 60 * swapT 6 + 2 * repairT + 23

/-- Beyond a fixed supplier-dependent dimension threshold, long records pay
shared-bank setup without an independent bank-size hypothesis. -/
theorem canonicalRouter_one_row_setup_le (n B : ℕ)
    (hlarge : canonicalRouterSetupThreshold ≤ n) (hB : (n + 2) ^ 2 ≤ B) :
    let width := n + canonicalScalarWidth 1 +
      canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
    6 * (swapT 6 * (width + 1)) + 2 * repairT + 6 * swapT 6 + 23 ≤ 2 ^ n * B := by
  have hb : n + 1 ≤ B := by nlinarith only [hB, Nat.zero_le n]
  have hbudget : 60 * swapT 6 + 2 * repairT + 23 ≤ 2 ^ n :=
    hlarge.trans (Nat.lt_two_pow_self (n := n)).le
  let width := n + canonicalScalarWidth 1 +
    canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
  have hw1 : canonicalScalarWidth 1 = 1 := by decide
  have hw : width + 1 ≤ 9 * B := by
    have h₁ := canonicalScalarWidth_le_self (3 * (n + canonicalScalarWidth 1 + B))
    have h₂ := canonicalScalarWidth_le_self n
    dsimp only [width]
    rw [hw1] at h₁ ⊢
    omega
  have bound (width B tapes repair N : ℕ) (hw : width + 1 ≤ 9 * B) (hb : 1 ≤ B)
      (hbudget : 60 * tapes + 2 * repair + 23 ≤ N) :
      6 * (tapes * (width + 1)) + 2 * repair + 6 * tapes + 23 ≤ N * B := by
    have hm := Nat.mul_le_mul_left (6 * tapes) hw
    have hf := Nat.mul_le_mul_left (2 * repair + 6 * tapes + 23) hb
    have hv := Nat.mul_le_mul_right B hbudget
    nlinarith only [hm, hf, hv]
  exact bound width B (swapT 6) repairT (2 ^ n) hw (by omega) hbudget

end IntegerMultBounds.MathlibTM2.Routing
