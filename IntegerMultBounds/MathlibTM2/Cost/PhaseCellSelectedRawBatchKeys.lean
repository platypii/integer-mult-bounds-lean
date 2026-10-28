module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawHeaderPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseBatchCaller

/-! Raw batch headers are paid once per complete key, including arbitrary cuts. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedRawHeaderCost_cuts_poly_le (ct : ℕ) (n : ℕ) (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target a b : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (ha : a ≤ Sizes.s n i) (hb : b ≤ Sizes.s n i)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    let p := Sizes.p n
    let s := Sizes.s n i
    let t := Sizes.t n i
    let l := haloInverseRingLog s t
    let W := inverseCallerWordWidth p u l target s t
    inverseScalarAtoms p s t u a b*tblC W 0+
      inverseMasterCopyCost W (inverseMasterValues p u l target s t a b)+
      inverseReleaseCost W (inverseMasterValues p u l target s t a b) ≤
        (20000*100000^3*(ct+21)^6)*t^6 := by
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let Z := (ct+21)*t
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have hpt : p ≤ t := selectedPrecision_le_axis h i
  have htZ : t ≤ Z := Nat.le_mul_of_pos_left t (by omega)
  have hZ : 1 ≤ Z := (hp.trans hpt).trans htZ
  have hpZ := hpt.trans htZ
  have huZ := hu.trans hpZ
  have hsZ := hst.le.trans htZ
  have hl := (haloInverseRingLog_bounds hp hst (h.quarter_p_le_theta i)).1
  have hlZ : l ≤ Z := hl.trans ((Nat.mul_le_mul_left 20 hpt).trans
    (Nat.mul_le_mul_right t (by omega : 20 ≤ ct+21)))
  have htargetZ : target ≤ Z := htarget.trans ((Nat.mul_le_mul_left ct hpt).trans
    (Nat.mul_le_mul_right t (by omega : ct ≤ ct+21)))
  have hheaders := inverseCallerHeaders_cuts_poly hZ hpZ huZ hlZ htargetZ hsZ htZ ha hb (hband.trans hsZ)
  exact hheaders.trans_eq (by dsimp only [Z]; ring)

noncomputable def selectedFamilyKeyHeaderCost (n : ℕ) (i : Fin (Sizes.d n))
    [NeZero (Sizes.s n i)] (ct : ℕ) (key : SelectedFamilyKey n i ct) : ℕ :=
  if PhaseCellBand.width (Sizes.p n) key.1 ≤ Sizes.s n i then
    let p := Sizes.p n
    let s := Sizes.s n i
    let t := Sizes.t n i
    let l := haloInverseRingLog s t
    let W := inverseCallerWordWidth p key.1 l key.2.1 s t
    inverseScalarAtoms p s t key.1 key.2.2.1 key.2.2.2*tblC W 0+
      inverseMasterCopyCost W (inverseMasterValues p key.1 l key.2.1 s t key.2.2.1 key.2.2.2)+
      inverseReleaseCost W (inverseMasterValues p key.1 l key.2.1 s t key.2.2.1 key.2.2.2)
  else 0

theorem selectedFamilyAllKeysHeaders_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)],
      scale*(∑ key : SelectedFamilyKey n i ct, selectedFamilyKeyHeaderCost n i ct key) ≤ Sizes.T n := by
  let K := 20000*100000^3*(ct+21)^6
  filter_upwards [selectedAxisPolynomial_le_volume (scale*2*(ct+1)*K) 2 8] with n hn
  intro h i _
  have hcost (key : SelectedFamilyKey n i ct) : selectedFamilyKeyHeaderCost n i ct key ≤ K*Sizes.t n i^6 := by
    unfold selectedFamilyKeyHeaderCost
    split_ifs with hband
    · exact selectedRawHeaderCost_cuts_poly_le ct n h i key.1 key.2.1 key.2.2.1 key.2.2.2
        (by omega) (by omega) (by omega) (by omega) hband
    · exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun key _ => hcost key)
  have hcard := selectedFamilyKey_card_le n h i ct
  have hpoly : (∑ key : SelectedFamilyKey n i ct, selectedFamilyKeyHeaderCost n i ct key) ≤
      (2*(ct+1)*K)*Sizes.t n i^8*Sizes.p n^2 := by
    calc
      _ ≤ Fintype.card (SelectedFamilyKey n i ct)*(K*Sizes.t n i^6) := by
        simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul] using hsum
      _ ≤ (2*(ct+1)*Sizes.t n i^2*Sizes.p n^2)*(K*Sizes.t n i^6) :=
        Nat.mul_le_mul_right _ hcard
      _ = (2*(ct+1)*K)*Sizes.t n i^8*Sizes.p n^2 := by ring
  exact (Nat.mul_le_mul_left scale hpoly).trans
    ((by convert hn i using 1 <;> ring) : scale*((2*(ct+1)*K)*Sizes.t n i^8*Sizes.p n^2) ≤ Sizes.T n)

theorem selectedFamilyDistinctKeysHeaders_volume_le (ct : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ keys : Finset (SelectedFamilyKey n i ct),
      (∑ key ∈ keys, selectedFamilyKeyHeaderCost n i ct key) ≤ Sizes.T n := by
  filter_upwards [selectedFamilyAllKeysHeaders_scaled_volume_le ct 1] with n hn
  intro h i _ keys
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ keys)
    (fun _ _ _ => Nat.zero_le _)).trans (by simpa only [one_mul] using hn h i)

theorem selectedRawFamilyKeyBatches_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (A : ℕ) (keys : Finset (SelectedFamilyKey n i ct))
        (replicas : SelectedFamilyKey n i ct → ℕ),
      (∀ key ∈ keys, PhaseCellBand.width (Sizes.p n) key.1 ≤ Sizes.s n i) →
      (∑ key ∈ keys, (familyInverseBatchCallerCost A
        (inverseCallerWordWidth (Sizes.p n) key.1
          (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) key.2.1 (Sizes.s n i) (Sizes.t n i))
        (Sizes.p n) key.1
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
        key.2.2.1 key.2.2.2 key.2.1 (replicas key) : ℝ)) ≤
      2*(Sizes.T n : ℝ)+∑ key ∈ keys, (replicas key : ℝ)*D*(Sizes.t n i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n) key.1 : ℝ)^2/Sizes.d n)*
          (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hbatch⟩ := selectedFamilyKeyBatches_fast_le ct
  refine ⟨D,hD,?_⟩
  filter_upwards [hbatch,selectedFamilyDistinctKeysHeaders_volume_le ct] with n hb hh
  intro h i _ A keys replicas hband
  have hheaders : (∑ key ∈ keys, (selectedFamilyKeyHeaderCost n i ct key : ℝ)) ≤ Sizes.T n := by
    exact_mod_cast hh h i keys
  have hclosed := hb h i A keys replicas hband
  have hsplit : (∑ key ∈ keys, (familyInverseBatchCallerCost A
        (inverseCallerWordWidth (Sizes.p n) key.1
          (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) key.2.1 (Sizes.s n i) (Sizes.t n i))
        (Sizes.p n) key.1 (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
        (Sizes.s n i) (Sizes.t n i) key.2.2.1 key.2.2.2 key.2.1 (replicas key) : ℝ)) =
      (∑ key ∈ keys, (selectedFamilyKeyHeaderCost n i ct key : ℝ))+
      (∑ key ∈ keys, (generatedClosedFamilyComplexBatchCost A (Sizes.p n) key.1
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
        key.2.2.1 key.2.2.2 key.2.1 (replicas key) : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro key hk
    simp only [familyInverseBatchCallerCost,selectedFamilyKeyHeaderCost,ite_eq_left (hband key hk),Nat.cast_add]
    ring
  rw [hsplit]
  have hc := add_le_add hheaders hclosed
  convert hc using 1 <;> ring

end IntegerMultBounds.MathlibTM2.Cost
