module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyDispatchCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawBatchKeys

/-! Link physical record costs to their complete numerical setup keys. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem sum_map_distinct_keys_le_univ {α β : Type} [Fintype β] [DecidableEq β]
    (records : List α) (key : α → β) (hkeys : (records.map key).Nodup) (f : β → ℕ) :
    (records.map (fun r => f (key r))).sum ≤ ∑ k, f k := by
  calc
    _ = ((records.map key).map f).sum := by rw [List.map_map]; rfl
    _ = (records.map key).toFinset.sum f := (List.sum_toFinset f hkeys).symm
    _ ≤ ∑ k, f k := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

theorem familyDispatchInput_cost_le {T A s : ℕ} [NeZero s] {p l t : ℕ} {d : ℝ}
    (work : Fin 303 → Fin T) (r : FamilyDispatchInput s A) (hr : FamilyDispatchReady p l t d r) :
    r.cost p l t work ≤ 16000*familyInverseBatchCallerCost A
      (inverseCallerWordWidth p r.u l r.target s t) p r.u l s t r.a r.b r.target r.inputs.length := by
  have hb := familyInverseBatch_bank_stock_le r.rawBank r.inputs [] r.scalarWidth hr.scalarWidth
    hr.scalars hr.blank (by simpa only [FamilyDispatchInput.rawBank,List.append_nil] using hr.source) hr.count
  have hstock : (∑ i, (r.words i).length) ≤
      303*(r.inputs.length*s*r.width p l t+inverseCallerWordWidth p r.u l r.target s t+r.inputs.length) := by
    simpa only [FamilyDispatchInput.rawBank,hr.outputBlank,List.length_nil,Nat.add_zero] using hb
  exact physicalFamilyDispatchCost_le work r.words hstock

def MatchesSelectedFamilyKey {n A : ℕ} {i : Fin (Sizes.d n)} {ct : ℕ}
    (r : FamilyDispatchInput (Sizes.s n i) A) (key : SelectedFamilyKey n i ct) : Prop :=
  r.u = key.1.val ∧ r.target = key.2.1.val ∧ r.a = key.2.2.1.val ∧ r.b = key.2.2.2.val

theorem selectedFamilyDispatchInput_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (work : Fin 303 → Fin T) (d : ℝ)
        (r : FamilyDispatchInput (Sizes.s n i) A) (key : SelectedFamilyKey n i ct),
      MatchesSelectedFamilyKey r key →
      FamilyDispatchReady (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) d r →
      (r.cost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work : ℝ) ≤
        16000*((selectedFamilyKeyHeaderCost n i ct key : ℝ)+(selectedFamilyKeySetupCost n i ct A key : ℝ))+
        (r.inputs.length : ℝ)*D*(Sizes.t n i : ℝ)*
          (1+(PhaseCellBand.width (Sizes.p n) r.u : ℝ)^2/Sizes.d n)*
            (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hbatch⟩ := selectedFamilyBatch_density_fast_le ct
  refine ⟨16000*D,mul_nonneg (by positivity) hD,?_⟩
  filter_upwards [hbatch] with n hn
  intro h i _ T A work d r key hk hr
  obtain ⟨hu,htarget,ha,hb⟩ := hk
  have huBound : r.u ≤ Sizes.p n := by rw [hu]; exact Nat.le_of_lt_succ key.1.isLt
  have htBound : r.target ≤ ct*Sizes.p n := by rw [htarget]; exact Nat.le_of_lt_succ key.2.1.isLt
  have hc := hn h i A r.u r.target r.a r.b r.inputs.length huBound htBound hr.band hr.a hr.b
  have hp : (r.cost (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i) work : ℝ) ≤
      16000*(familyInverseBatchCallerCost A
        (inverseCallerWordWidth (Sizes.p n) r.u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) r.target (Sizes.s n i) (Sizes.t n i))
        (Sizes.p n) r.u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
        r.a r.b r.target r.inputs.length : ℝ) := by exact_mod_cast familyDispatchInput_cost_le work r hr
  have hheader : selectedFamilyKeyHeaderCost n i ct key =
      inverseScalarAtoms (Sizes.p n) (Sizes.s n i) (Sizes.t n i) r.u r.a r.b*
        tblC (inverseCallerWordWidth (Sizes.p n) r.u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) r.target (Sizes.s n i) (Sizes.t n i)) 0+
      inverseMasterCopyCost (inverseCallerWordWidth (Sizes.p n) r.u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) r.target (Sizes.s n i) (Sizes.t n i))
        (inverseMasterValues (Sizes.p n) r.u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) r.target (Sizes.s n i) (Sizes.t n i) r.a r.b)+
      inverseReleaseCost (inverseCallerWordWidth (Sizes.p n) r.u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) r.target (Sizes.s n i) (Sizes.t n i))
        (inverseMasterValues (Sizes.p n) r.u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) r.target (Sizes.s n i) (Sizes.t n i) r.a r.b) := by
    simp only [selectedFamilyKeyHeaderCost,← hu,← htarget,← ha,← hb,ite_eq_left hr.band]
  have hsetup : selectedFamilyKeySetupCost n i ct A key =
      generatedFamilyComplexSetupCostBound A (Sizes.p n) r.u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) (Sizes.t n i) r.a r.b r.target := by
    simp only [selectedFamilyKeySetupCost,← hu,← htarget,← ha,← hb,ite_eq_left hr.band]
  rw [hheader,hsetup]
  dsimp only at hc
  unfold familyInverseBatchCallerCost at hp
  push_cast at hp ⊢
  nlinarith only [hp,hc]

end IntegerMultBounds.MathlibTM2.Cost
