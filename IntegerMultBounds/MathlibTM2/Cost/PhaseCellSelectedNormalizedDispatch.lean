module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellNormalizedDispatchCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedDispatchRecords
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedDispatchStock

/-! Fixed-factor transfer preserves the selected normalized dispatch's fast and stock envelopes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedNormalizedDispatchLedger_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (work : Fin 303 → Fin T) (d : ℝ)
        (records : List (FamilyDispatchInput (Sizes.s n i) A))
        (key : FamilyDispatchInput (Sizes.s n i) A → SelectedFamilyKey n i ct),
      (records.map key).Nodup → (∀ r ∈ records, MatchesSelectedFamilyKey r (key r)) →
      (∀ r ∈ records, FamilyDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d r) →
      (((records.map (fun r => r.normalizedCost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work+3)).sum+
          6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 : ℕ) : ℝ) ≤
        576000*(Sizes.T n : ℝ)+(records.map (fun r => (r.inputs.length : ℝ)*D*(Sizes.t n i : ℝ)*
          (1+(PhaseCellBand.width (Sizes.p n) r.u : ℝ)^2/Sizes.d n)*
            (Sizes.p n : ℝ)^(129/128 : ℝ))).sum+90 := by
  obtain ⟨D,hD,hraw⟩ := selectedFamilyDispatchLedger_fast_le ct
  refine ⟨9*D,mul_nonneg (by norm_num) hD,?_⟩
  filter_upwards [hraw] with n hn
  intro h i _ T A work d records key hkeys hmatch hready
  have hr := hn h i T A work d records key hkeys hmatch hready
  have hcost := normalizedDispatch_time_ledger_le (Sizes.p n)
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work records
  have hreal : (((records.map (fun r => r.normalizedCost (Sizes.p n)
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work+3)).sum+
      6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 : ℕ) : ℝ) ≤
    9*(((records.map (fun r => r.cost (Sizes.p n)
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work+3)).sum+
      6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+10 : ℕ) : ℝ) := by
    exact_mod_cast hcost
  have hsum : (records.map (fun r => (r.inputs.length : ℝ)*(9*D)*(Sizes.t n i : ℝ)*
      (1+(PhaseCellBand.width (Sizes.p n) r.u : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ))).sum =
    9*(records.map (fun r => (r.inputs.length : ℝ)*D*(Sizes.t n i : ℝ)*
      (1+(PhaseCellBand.width (Sizes.p n) r.u : ℝ)^2/Sizes.d n)*(Sizes.p n : ℝ)^(129/128 : ℝ))).sum := by
    rw [←List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro r _
    ring
  rw [hsum]
  nlinarith only [hreal,hr]

theorem selectedNormalizedDispatchStockLedger_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (work : Fin 303 → Fin T) (d : ℝ)
        (records : List (FamilyDispatchInput (Sizes.s n i) A))
        (key : FamilyDispatchInput (Sizes.s n i) A → SelectedFamilyKey n i ct),
      (records.map key).Nodup → (∀ r ∈ records, MatchesSelectedFamilyKey r (key r)) →
      (∀ r ∈ records, FamilyDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d r) →
      scale*((records.map (fun r => r.normalizedStock (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work)).sum+
          6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8) ≤
        288000*scale*(records.map (fun r => r.inputs.length*Sizes.s n i*
          r.width (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i))).sum+Sizes.T n := by
  filter_upwards [selectedFamilyDispatchStockLedger_scaled_volume_le ct (9*scale)] with n hn
  intro h i _ T A work d records key hkeys hmatch hready
  have hc := hn h i T A work d records key hkeys hmatch hready
  have hl := Nat.mul_le_mul_left scale
    (normalizedDispatch_stock_ledger_le (Sizes.p n)
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work records)
  nlinarith only [hc,hl]

end IntegerMultBounds.MathlibTM2.Cost
