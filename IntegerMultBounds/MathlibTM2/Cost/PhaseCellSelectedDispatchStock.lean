module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyDispatchStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedStepKeys

/-! The complete distinct-key dispatcher has one box-volume allowance plus linear batch stock. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedFamilyDispatchInput_stock_le {n T A ct : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (work : Fin 303 → Fin T) (d : ℝ)
    (r : FamilyDispatchInput (Sizes.s n i) A) (key : SelectedFamilyKey n i ct)
    (hk : MatchesSelectedFamilyKey r key)
    (hr : FamilyDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d r) :
    r.stock (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work ≤
      16000*selectedFamilyKeyHeaderCost n i ct key+selectedFamilyKeySetupCost n i ct A key+
      selectedFamilyKeyStepCost n i ct A key+
      16000*(r.inputs.length*Sizes.s n i*r.width (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i)) := by
  obtain ⟨hu,htarget,ha,hb⟩ := hk
  have hh : selectedFamilyKeyHeaderCost n i ct key =
      familyDispatchHeaderCost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) r := by
    simp only [selectedFamilyKeyHeaderCost,familyDispatchHeaderCost,← hu,← htarget,← ha,← hb,ite_eq_left hr.band]
  rw [hh]
  simp only [selectedFamilyKeySetupCost,selectedFamilyKeyStepCost,← hu,← htarget,← ha,← hb,ite_eq_left hr.band]
  exact familyDispatchInput_stock_le (h.good.lt i) work r hr

theorem selectedFamilyDispatchStock_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (work : Fin 303 → Fin T) (d : ℝ)
        (records : List (FamilyDispatchInput (Sizes.s n i) A))
        (key : FamilyDispatchInput (Sizes.s n i) A → SelectedFamilyKey n i ct),
      (records.map key).Nodup → (∀ r ∈ records, MatchesSelectedFamilyKey r (key r)) →
      (∀ r ∈ records, FamilyDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d r) →
      scale*(records.map (fun r => r.stock (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work)).sum ≤
        16000*scale*(records.map (fun r => r.inputs.length*Sizes.s n i*
          r.width (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i))).sum+Sizes.T n := by
  filter_upwards [selectedFamilyAllKeysHeaders_scaled_volume_le ct (3*16000*scale),
    selectedFamilyAllKeysSetup_scaled_volume_le ct (3*scale),
    selectedFamilyAllKeysStep_scaled_volume_le ct (3*scale)] with n hh hs hk
  intro h i _ T A work d records key hkeys hmatch hready
  have hheaders := (Nat.mul_le_mul_left (3*16000*scale)
    (sum_map_distinct_keys_le_univ records key hkeys (selectedFamilyKeyHeaderCost n i ct))).trans (hh h i)
  have hsetup := (Nat.mul_le_mul_left (3*scale)
    (sum_map_distinct_keys_le_univ records key hkeys (selectedFamilyKeySetupCost n i ct A))).trans (hs h i A)
  have hstep := (Nat.mul_le_mul_left (3*scale)
    (sum_map_distinct_keys_le_univ records key hkeys (selectedFamilyKeyStepCost n i ct A))).trans (hk h i A)
  have hsum := List.sum_le_sum (l := records) (fun r hr =>
    selectedFamilyDispatchInput_stock_le h i work d r (key r) (hmatch r hr) (hready r hr))
  simp only [List.sum_map_add,List.sum_map_mul_left] at hsum
  have hscaled := Nat.mul_le_mul_left scale hsum
  nlinarith only [hscaled,hheaders,hsetup,hstep]

theorem familyDispatchInput_restore_le_stock {T A s : ℕ} [NeZero s]
    (p l t : ℕ) (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) :
    2*(descriptorBankTape (placedDescriptorFields work r.words)).length+6 ≤ r.stock p l t work := by
  rw [descriptorBankTape_length]
  simp only [placedDescriptorFields,List.map_ofFn,Function.comp_def,List.sum_ofFn,List.length_ofFn]
  unfold FamilyDispatchInput.stock
  rw [takePlacedDescriptorBankCost_eq]
  omega

theorem familyDispatch_stock_ledger_le {T A s : ℕ} [NeZero s]
    (p l t : ℕ) (work : Fin 303 → Fin T) (records : List (FamilyDispatchInput s A)) :
    (records.map (fun r => r.stock p l t work)).sum+6*records.length+
        2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8 ≤
      2*(records.map (fun r => r.stock p l t work)).sum+8 := by
  induction records with
  | nil => simp [descriptorScheduleTape]
  | cons r records ih =>
    have hc := familyDispatchInput_restore_le_stock p l t work r
    simp only [List.map_cons,List.sum_cons,List.length_cons,descriptorScheduleTape,
      List.flatMap_cons,List.length_append] at ih ⊢
    omega

theorem selectedFamilyDispatchStockLedger_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (work : Fin 303 → Fin T) (d : ℝ)
        (records : List (FamilyDispatchInput (Sizes.s n i) A))
        (key : FamilyDispatchInput (Sizes.s n i) A → SelectedFamilyKey n i ct),
      (records.map key).Nodup → (∀ r ∈ records, MatchesSelectedFamilyKey r (key r)) →
      (∀ r ∈ records, FamilyDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d r) →
      scale*((records.map (fun r => r.stock (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work)).sum+
          6*records.length+2*(descriptorScheduleTape work FamilyDispatchInput.words records).length+8) ≤
        32000*scale*(records.map (fun r => r.inputs.length*Sizes.s n i*
          r.width (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i))).sum+Sizes.T n := by
  filter_upwards [selectedFamilyDispatchStock_scaled_volume_le ct (4*scale),
    selectedAxisPolynomial_le_volume (16*scale) 0 0] with n hs hv
  intro h i _ T A work d records key hkeys hmatch hready
  have hc := hs h i T A work d records key hkeys hmatch hready
  have hf : 16*scale ≤ Sizes.T n := by simpa only [pow_zero,mul_one] using hv i
  have hl := Nat.mul_le_mul_left scale
    (familyDispatch_stock_ledger_le (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work records)
  nlinarith only [hc,hf,hl]

end IntegerMultBounds.MathlibTM2.Cost
