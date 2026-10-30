module

public import IntegerMultBounds.NLogN.PhaseCellCoreSetupGroups
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupKeys

/-! Generated core halos use the production complete setup key. Endpoint-key
regrouping therefore reuses exactly the selected family setup allowance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellMatrix
open scoped BigOperators

def selectedCoreSetupKey (N : ℕ) (i : Fin (Sizes.d N)) (ct : ℕ)
    (u : Fin (Sizes.p N+1)) (target : Fin (ct*Sizes.p N+1))
    (width band depth k : ℕ) : SelectedFamilyKey N i ct :=
  let endpoints := coreHaloEndpoints (Sizes.s N i) width k band depth
  have hb := coreHaloEndpoints_bounds (Sizes.s N i) width k band depth
  (u,target,⟨endpoints.1,by dsimp [endpoints]; omega⟩,⟨endpoints.2,by dsimp [endpoints]; omega⟩)

/-- With numerical parameters fixed, endpoint equality is precisely equality of
complete production keys. A movement length is absent from this equivalence. -/
theorem selectedCoreSetupKey_eq_iff (N : ℕ) (i : Fin (Sizes.d N)) (ct : ℕ)
    (u : Fin (Sizes.p N+1)) (target : Fin (ct*Sizes.p N+1))
    (width band depth k j : ℕ) :
    selectedCoreSetupKey N i ct u target width band depth k =
      selectedCoreSetupKey N i ct u target width band depth j ↔
    coreHaloEndpoints (Sizes.s N i) width k band depth =
      coreHaloEndpoints (Sizes.s N i) width j band depth := by
  simp [selectedCoreSetupKey,Prod.ext_iff,Fin.ext_iff]

def selectedCoreSetupKeys (N : ℕ) (i : Fin (Sizes.d N)) (ct : ℕ)
    (u : Fin (Sizes.p N+1)) (target : Fin (ct*Sizes.p N+1))
    (width band depth : ℕ) : Finset (SelectedFamilyKey N i ct) :=
  (coreIndices (Sizes.s N i) width).toFinset.image
    (selectedCoreSetupKey N i ct u target width band depth)

/-- This charges one setup per distinct complete key. The executed scheduler
must implement that multiplicity; this bound does not provide a reordering. -/
theorem selectedCoreSetupKeys_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ (h : Sizes.Big N) (i : Fin (Sizes.d N)),
      ∀ [NeZero (Sizes.s N i)], ∀ A : ℕ,
      ∀ (u : Fin (Sizes.p N+1)) (target : Fin (ct*Sizes.p N+1)) (width band depth : ℕ),
      scale*(∑ key ∈ selectedCoreSetupKeys N i ct u target width band depth,
        selectedFamilyKeySetupCost N i ct A key) ≤ Sizes.T N := by
  obtain ⟨C,hcost⟩ := selectedFamilyKeySetupCost_poly_le ct
  filter_upwards [hcost,selectedFamilyDistinctKeyCharges_scaled_volume_le ct scale C 6 4] with N hc hn
  intro h i _ A u target width band depth
  exact hn h i (selectedFamilyKeySetupCost N i ct A) (hc h i A)
    (selectedCoreSetupKeys N i ct u target width band depth)

end IntegerMultBounds.MathlibTM2.Cost
