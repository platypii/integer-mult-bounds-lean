module

public import IntegerMultBounds.MathlibTM2.Routing.PermutationMatchingTableBinary
public import IntegerMultBounds.MathlibTM2.Routing.SetupAbsorption

/-! Polynomial setup and volume absorption for the executed matching-table
compiler, proved over arbitrary dimensions before canonical widths are chosen. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

theorem permutationMatchingTableBinaryCost_le_fourth (N L x : ℕ)
    (hN : N ≤ x) (hL : L ≤ x) (hx : 1 ≤ x) :
    permutationMatchingTableBinaryCost N L ≤ 693 * x ^ 4 := by
  have hm : permutationMatchingTableBinaryCost N L ≤ permutationMatchingTableBinaryCost x x := by
    unfold permutationMatchingTableBinaryCost
    gcongr
  have he : permutationMatchingTableBinaryCost x x =
      90 * x ^ 4 + 201 * x ^ 3 + 199 * x ^ 2 + 161 * x + 42 := by
    unfold permutationMatchingTableBinaryCost
    ring
  have hx3 : x ^ 3 ≤ x ^ 4 := Nat.pow_le_pow_right hx (by decide : 3 ≤ 4)
  have hx2 : x ^ 2 ≤ x ^ 4 := Nat.pow_le_pow_right hx (by decide : 2 ≤ 4)
  have hx1 : x ≤ x ^ 4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hx (by decide : 1 ≤ 4)
  have hx0 : 1 ≤ x ^ 4 := Nat.one_le_pow _ _ hx
  rw [he] at hm
  nlinarith only [hm, hx3, hx2, hx1, hx0]

/-- Any compact dimension-width convention bounded by n+1 gives uniform
polynomial setup for the actual table program. -/
theorem permutationMatchingTableBinaryCost_polynomial (width : ℕ → ℕ)
    (hwidth : ∀ n, width n ≤ n + 1) (n : ℕ) :
    permutationMatchingTableBinaryCost n (width n) ≤ 693 * (n + 1) ^ 4 :=
  permutationMatchingTableBinaryCost_le_fourth n (width n) (n + 1)
    (Nat.le_succ n) (hwidth n) (Nat.succ_le_succ (Nat.zero_le n))

/-- Repeated compiler setup is eventually paid by routed volume, uniformly
in row count and positive payload width. -/
theorem permutationMatchingTableBinaryCost_eventually_le_volume (width : ℕ → ℕ)
    (hwidth : ∀ n, width n ≤ n + 1) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ R B : ℕ, 1 ≤ B →
      R * permutationMatchingTableBinaryCost n (width n) ≤ R * 2 ^ n * B :=
  repeatedPolynomialSetup_eventually_le_volume (fun n => permutationMatchingTableBinaryCost n (width n))
    693 4 (permutationMatchingTableBinaryCost_polynomial width hwidth)

end IntegerMultBounds.MathlibTM2.Routing
