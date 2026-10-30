module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupKeys

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult

/-- Rebuilding setup per tile is cheap when the tile capacity pays one setup.
The last partial tile is paid by one additional setup. -/
theorem tiled_setup_cost_le (N B S : ℕ) (hB : 0 < B) (hS : S ≤ B) :
    ((N+B-1)/B)*S ≤ N+S := by
  have hc : (N+B-1)/B ≤ N/B+1 := by
    have hh : (N+B-1)/B ≤ (N+B)/B := Nat.div_le_div_right (show N+B-1 ≤ N+B by omega)
    simpa only [Nat.add_div_right N hB] using hh
  calc
    _ ≤ (N/B+1)*S := Nat.mul_le_mul_right S hc
    _ = (N/B)*S+S := by ring
    _ ≤ (N/B)*B+S := Nat.add_le_add_right (Nat.mul_le_mul_left (N/B) hS) S
    _ ≤ N+S := Nat.add_le_add_right (Nat.div_mul_le_self N B) S

/-- Padding only the final replica tile adds at most one tile of traffic.
This is additive overhead, not padding the whole replica axis to a square. -/
theorem tiled_payload_volume_le (N B W : ℕ) :
    ((N+B-1)/B)*B*W ≤ N*W+B*W := by
  calc
    _ ≤ (N+B-1)*W := Nat.mul_le_mul_right W (Nat.div_mul_le_self _ _)
    _ ≤ (N+B)*W := Nat.mul_le_mul_right W (Nat.sub_le _ _)
    _ = N*W+B*W := Nat.add_mul _ _ _

/-- A polynomial-size padded tile contributes only one whole-box allowance,
regardless of the replica count. The caller supplies its actual tile-size bound. -/
theorem selectedTiledPayload_volume_le (C a b : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (Sizes.d n)) (N B W : ℕ),
      B*W ≤ C*Sizes.t n i^a*Sizes.p n^b →
      ((N+B-1)/B)*B*W ≤ N*W+Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume C b a] with n hn
  intro i N B W htile
  exact (tiled_payload_volume_le N B W).trans
    (Nat.add_le_add_left (htile.trans (hn i)) _)

/-- Selected setup, even over every admissible key, fits one polynomial-size
replica tile. The arbitrary scale can pay a fixed number of setup/release passes. -/
theorem selectedFamilyAllKeysSetup_tile_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ,
      scale*(∑ key : SelectedFamilyKey n i ct, selectedFamilyKeySetupCost n i ct A key) ≤
        Sizes.t n i^9 := by
  obtain ⟨C,hcost⟩ := selectedFamilyAllKeysSetup_poly_le ct
  filter_upwards [hcost,selectedAxis_eventually_polynomial (scale*C) 6] with n hc hp
  intro h i _ A
  calc
    _ ≤ scale*(C*Sizes.t n i^8*Sizes.p n^6) := Nat.mul_le_mul_left scale (hc h i A)
    _ = ((scale*C)*Sizes.p n^6)*Sizes.t n i^8 := by ring
    _ ≤ Sizes.t n i*Sizes.t n i^8 := Nat.mul_le_mul_right _ (hp i)
    _ = Sizes.t n i^9 := by ring

/-- Rebuild all selected setups per axis-polynomial replica tile. Total setup
is paid by the replica count plus a single whole-box setup allowance. Thus the
scheduler need not transpose an arbitrarily long replica axis in one operation. -/
theorem selectedFamilyTiledSetup_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ (A N B : ℕ) (keys : Finset (SelectedFamilyKey n i ct)),
      Sizes.t n i^9 ≤ B →
      ((N+B-1)/B)*
        (scale*∑ key ∈ keys, selectedFamilyKeySetupCost n i ct A key) ≤ N+Sizes.T n := by
  filter_upwards [selectedFamilyAllKeysSetup_tile_le ct scale,
    selectedFamilyAllKeysSetup_scaled_volume_le ct scale] with n ht hv
  intro h i _ A N B keys hB
  have hsub : scale*(∑ key ∈ keys, selectedFamilyKeySetupCost n i ct A key) ≤
      scale*(∑ key : SelectedFamilyKey n i ct, selectedFamilyKeySetupCost n i ct A key) := by
    apply Nat.mul_le_mul_left
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ keys) (fun _ _ _ => Nat.zero_le _)
  have hpos : 0 < B := by
    have haxis : 0 < Sizes.t n i^9 := by
      have hh := h.good.lt i
      have hs := NeZero.pos (Sizes.s n i)
      have ht : 0 < Sizes.t n i := hs.trans hh
      positivity
    omega
  exact (tiled_setup_cost_le N _ _ hpos ((hsub.trans (ht h i A)).trans hB)).trans
    (Nat.add_le_add_left (hsub.trans (hv h i A)) N)

end IntegerMultBounds.MathlibTM2.Cost
