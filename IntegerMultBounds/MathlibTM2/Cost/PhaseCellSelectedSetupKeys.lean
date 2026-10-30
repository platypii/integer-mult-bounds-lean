module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Price all admissible selected setup keys, without a replica lower bound.
The one-time ledger below assumes each key is initialized once.
`PhaseCellTiledSetupKeys` separately pays repeated initialization per large replica tile. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- The varying numerical and halo parameters at one selected axis. All other
setup parameters are fixed or derived by the generated family entry. -/
abbrev SelectedFamilyKey (n : ℕ) (i : Fin (Sizes.d n)) (ct : ℕ) :=
  Fin (Sizes.p n+1) × Fin (ct*Sizes.p n+1) ×
    Fin (Sizes.s n i+1) × Fin (Sizes.s n i+1)

noncomputable def selectedFamilyKeySetupCost (n : ℕ) (i : Fin (Sizes.d n))
    [NeZero (Sizes.s n i)] (ct A : ℕ) (key : SelectedFamilyKey n i ct) : ℕ :=
  if PhaseCellBand.width (Sizes.p n) key.1 ≤ Sizes.s n i then
    generatedFamilyComplexSetupCostBound A (Sizes.p n) key.1
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) (Sizes.t n i) key.2.2.1 key.2.2.2 key.2.1
  else 0

theorem selectedFamilyKey_card_le (n : ℕ) (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) (ct : ℕ) :
    Fintype.card (SelectedFamilyKey n i ct) ≤
      2*(ct+1)*Sizes.t n i^2*Sizes.p n^2 := by
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hs : Sizes.s n i+1 ≤ Sizes.t n i := h.good.lt i
  have hp' : Sizes.p n+1 ≤ 2*Sizes.p n := by omega
  have ht : ct*Sizes.p n+1 ≤ (ct+1)*Sizes.p n := by nlinarith
  have hh := Nat.mul_le_mul hp' (Nat.mul_le_mul ht (Nat.mul_le_mul hs hs))
  simpa only [SelectedFamilyKey,Fintype.card_prod,Fintype.card_fin] using
    hh.trans_eq (by ring)

theorem selectedFamilyKeySetupCost_poly_le (ct : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n)
      (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ,
      ∀ key : SelectedFamilyKey n i ct,
      selectedFamilyKeySetupCost n i ct A key ≤ C*Sizes.t n i^6*Sizes.p n^4 := by
  obtain ⟨C,hC,hsetup⟩ := selectedFamilySetup_poly_le ct
  refine ⟨⌈C⌉₊,?_⟩
  filter_upwards [hsetup] with n hn
  intro h i _ A key
  unfold selectedFamilyKeySetupCost
  split_ifs with hband
  · have hc := hn h i A key.1 key.2.1 key.2.2.1 key.2.2.2
      (by omega) (by omega) hband (by omega) (by omega)
    dsimp only at hc
    have hm : C*(Sizes.t n i : ℝ)^6*(Sizes.p n : ℝ)^4 ≤
        (⌈C⌉₊ : ℝ)*(Sizes.t n i : ℝ)^6*(Sizes.p n : ℝ)^4 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity)) (by positivity)
    exact_mod_cast hc.trans hm
  · exact Nat.zero_le _

/-- The explicit axis polynomial is useful when setup is rebuilt per large
replica tile, rather than only once for the whole tensor. -/
theorem selectedFamilyAllKeysSetup_poly_le (ct : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ,
      (∑ key : SelectedFamilyKey n i ct, selectedFamilyKeySetupCost n i ct A key) ≤
        C*Sizes.t n i^8*Sizes.p n^6 := by
  obtain ⟨C,hcost⟩ := selectedFamilyKeySetupCost_poly_le ct
  refine ⟨2*(ct+1)*C,?_⟩
  filter_upwards [hcost] with n hc
  intro h i _ A
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun key _ => hc h i A key)
  have hcard := selectedFamilyKey_card_le n h i ct
  calc
    _ ≤ Fintype.card (SelectedFamilyKey n i ct)*(C*Sizes.t n i^6*Sizes.p n^4) := by
      simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using hsum
    _ ≤ (2*(ct+1)*Sizes.t n i^2*Sizes.p n^2)*(C*Sizes.t n i^6*Sizes.p n^4) :=
      Nat.mul_le_mul_right _ hcard
    _ = (2*(ct+1)*C)*Sizes.t n i^8*Sizes.p n^6 := by ring

theorem selectedFamilyAllKeysSetup_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ,
      scale*(∑ key : SelectedFamilyKey n i ct, selectedFamilyKeySetupCost n i ct A key) ≤ Sizes.T n := by
  obtain ⟨C,hcost⟩ := selectedFamilyAllKeysSetup_poly_le ct
  filter_upwards [hcost,selectedAxisPolynomial_le_volume (scale*C) 6 8] with n hc hv
  intro h i _ A
  exact (Nat.mul_le_mul_left scale (hc h i A)).trans
    ((by convert hv i using 1 <;> ring) : scale*(C*Sizes.t n i^8*Sizes.p n^6) ≤ Sizes.T n)

theorem selectedFamilyAllKeysSetup_volume_le (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ,
      (∑ key : SelectedFamilyKey n i ct, selectedFamilyKeySetupCost n i ct A key) ≤ Sizes.T n := by
  simpa only [one_mul] using selectedFamilyAllKeysSetup_scaled_volume_le ct 1

/-- Any distinct-key subfamily pays no more setup than the complete family. -/
theorem selectedFamilyDistinctKeysSetup_volume_le (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ A : ℕ, ∀ keys : Finset (SelectedFamilyKey n i ct),
      (∑ key ∈ keys, selectedFamilyKeySetupCost n i ct A key) ≤ Sizes.T n := by
  filter_upwards [selectedFamilyAllKeysSetup_volume_le ct] with n hn
  intro h i _ A keys
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ keys)
    (fun _ _ _ => Nat.zero_le _)).trans (hn h i A)

/-- The executed batch ledger summed over any distinct admissible keys. The
one-time setup for the entire subfamily is paid by one whole-box volume. -/
theorem selectedFamilyKeyBatches_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (A : ℕ) (keys : Finset (SelectedFamilyKey n i ct))
        (replicas : SelectedFamilyKey n i ct → ℕ),
      (∀ key ∈ keys, PhaseCellBand.width (Sizes.p n) key.1 ≤ Sizes.s n i) →
      (∑ key ∈ keys, (generatedClosedFamilyComplexBatchCost A (Sizes.p n) key.1
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
        key.2.2.1 key.2.2.2 key.2.1 (replicas key) : ℝ)) ≤
      (Sizes.T n : ℝ)+∑ key ∈ keys, (replicas key : ℝ)*D*(Sizes.t n i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n) key.1 : ℝ)^2/Sizes.d n)*
          (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hbatch⟩ := selectedFamilyBatch_density_fast_le ct
  refine ⟨D,hD,?_⟩
  filter_upwards [hbatch,selectedFamilyDistinctKeysSetup_volume_le ct] with n hb hs
  intro h i _ A keys replicas hband
  have hsum := Finset.sum_le_sum (s := keys) (fun key hk =>
    hb h i A key.1 key.2.1 key.2.2.1 key.2.2.2 (replicas key)
      (by omega) (by omega) (hband key hk) (by omega) (by omega))
  rw [Finset.sum_add_distrib] at hsum
  have hsetup : (∑ key ∈ keys, (generatedFamilyComplexSetupCostBound A (Sizes.p n) key.1
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
      key.2.2.1 key.2.2.2 key.2.1 : ℝ)) ≤ Sizes.T n := by
    have hc : ((∑ key ∈ keys, selectedFamilyKeySetupCost n i ct A key : ℕ) : ℝ) ≤ Sizes.T n := by
      exact_mod_cast hs h i A keys
    push_cast at hc
    convert hc using 1
    apply Finset.sum_congr rfl
    intro key hk
    simp only [selectedFamilyKeySetupCost,if_pos (hband key hk)]
  exact hsum.trans (add_le_add hsetup le_rfl)

end IntegerMultBounds.MathlibTM2.Cost
