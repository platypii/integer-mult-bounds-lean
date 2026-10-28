module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyDispatchKeys

/-! Distinct complete keys price the actual executed record list, including final restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedFamilyDispatchRecords_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (work : Fin 303 → Fin T) (d : ℝ)
        (records : List (FamilyDispatchInput (Sizes.s n i) A))
        (key : FamilyDispatchInput (Sizes.s n i) A → SelectedFamilyKey n i ct),
      (records.map key).Nodup → (∀ r ∈ records, MatchesSelectedFamilyKey r (key r)) →
      (∀ r ∈ records, FamilyDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d r) →
      ((records.map (fun r => r.cost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work)).sum : ℝ) ≤
        32000*(Sizes.T n : ℝ)+(records.map (fun r => (r.inputs.length : ℝ)*D*(Sizes.t n i : ℝ)*
          (1+(PhaseCellBand.width (Sizes.p n) r.u : ℝ)^2/Sizes.d n)*
            (Sizes.p n : ℝ)^(129/128 : ℝ))).sum := by
  obtain ⟨D,hD,hinput⟩ := selectedFamilyDispatchInput_fast_le ct
  refine ⟨D,hD,?_⟩
  filter_upwards [hinput,selectedFamilyAllKeysHeaders_scaled_volume_le ct 1,
    selectedFamilyAllKeysSetup_volume_le ct] with n hi hh hs
  intro h i _ T A work d records key hkeys hmatch hready
  have hheadersNat := (sum_map_distinct_keys_le_univ records key hkeys
    (selectedFamilyKeyHeaderCost n i ct)).trans (by simpa only [one_mul] using hh h i)
  have hsetupNat := (sum_map_distinct_keys_le_univ records key hkeys
    (selectedFamilyKeySetupCost n i ct A)).trans (hs h i A)
  have hheaders : (records.map (fun r => (selectedFamilyKeyHeaderCost n i ct (key r) : ℝ))).sum ≤ Sizes.T n := by
    have hc : (((records.map (fun r => selectedFamilyKeyHeaderCost n i ct (key r))).sum : ℕ) : ℝ) ≤ Sizes.T n := by
      exact_mod_cast hheadersNat
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hc
  have hsetup : (records.map (fun r => (selectedFamilyKeySetupCost n i ct A (key r) : ℝ))).sum ≤ Sizes.T n := by
    have hc : (((records.map (fun r => selectedFamilyKeySetupCost n i ct A (key r))).sum : ℕ) : ℝ) ≤ Sizes.T n := by
      exact_mod_cast hsetupNat
    simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def] using hc
  have hsum := List.sum_le_sum (l := records) (fun r hr =>
    hi h i T A work d r (key r) (hmatch r hr) (hready r hr))
  simp only [List.sum_map_add,List.sum_map_mul_left] at hsum
  nlinarith only [hsum,hheaders,hsetup]

theorem selectedFamilyDispatchLedger_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (work : Fin 303 → Fin T) (d : ℝ)
        (records : List (FamilyDispatchInput (Sizes.s n i) A))
        (key : FamilyDispatchInput (Sizes.s n i) A → SelectedFamilyKey n i ct),
      (records.map key).Nodup → (∀ r ∈ records, MatchesSelectedFamilyKey r (key r)) →
      (∀ r ∈ records, FamilyDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d r) →
      (((records.map (fun r => r.cost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work+3)).sum+
          6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 : ℕ) : ℝ) ≤
        64000*(Sizes.T n : ℝ)+(records.map (fun r => (r.inputs.length : ℝ)*D*(Sizes.t n i : ℝ)*
          (1+(PhaseCellBand.width (Sizes.p n) r.u : ℝ)^2/Sizes.d n)*
            (Sizes.p n : ℝ)^(129/128 : ℝ))).sum+10 := by
  obtain ⟨D,hD,hrecords⟩ := selectedFamilyDispatchRecords_fast_le ct
  refine ⟨2*D,mul_nonneg (by positivity) hD,?_⟩
  filter_upwards [hrecords] with n hn
  intro h i _ T A work d records key hkeys hmatch hready
  have hc := hn h i T A work d records key hkeys hmatch hready
  have hl : (((records.map (fun r => r.cost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work+3)).sum+
          6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 : ℕ) : ℝ) ≤
      2*((records.map (fun r => r.cost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work)).sum : ℝ)+10 := by
    have hnat := familyDispatch_restore_ledger_le (Sizes.p n)
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work records
    have hcast : (((records.map (fun r => r.cost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work+3)).sum+
          6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 : ℕ) : ℝ) ≤
      ((2*(records.map (fun r => r.cost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work)).sum+10 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_list_sum,List.map_map,Function.comp_def] using hcast
  have hsum : (records.map (fun r => (r.inputs.length : ℝ)*(2*D)*(Sizes.t n i : ℝ)*
      (1+(PhaseCellBand.width (Sizes.p n) r.u : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ))).sum =
      2*(records.map (fun r => (r.inputs.length : ℝ)*D*(Sizes.t n i : ℝ)*
      (1+(PhaseCellBand.width (Sizes.p n) r.u : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ))).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro r hr
    ring
  rw [hsum]
  nlinarith only [hl,hc]

end IntegerMultBounds.MathlibTM2.Cost
