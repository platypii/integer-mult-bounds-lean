module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPhysicalDispatchCost

/-! The complete-key time envelope includes actual descriptor traffic and bank cleanup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedPhysicalFamilyKeyBatches_fast_le (ct : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (T A : ℕ) (keys : Finset (SelectedFamilyKey n i ct))
        (replicas : SelectedFamilyKey n i ct → ℕ)
        (work : Fin 303 → Fin T) (words : SelectedFamilyKey n i ct → Fin 303 → List (Fin (A+4))),
      (∀ key ∈ keys, PhaseCellBand.width (Sizes.p n) key.1 ≤ Sizes.s n i) →
      (∀ key ∈ keys,
        let p := Sizes.p n
        let s := Sizes.s n i
        let t := Sizes.t n i
        let l := haloInverseRingLog s t
        let bits := boundaryTableBits p (boundaryRecoveryTarget p (key.2.1+1)) 2
          (haloBoundary s t (PhaseCellBand.width p key.1) key.2.2.1 key.2.2.2).card
        let w := executionWidth p l (initialSchurTarget p key.1 bits 2) 2
        let W := inverseCallerWordWidth p key.1 l key.2.1 s t
        (∑ j, ((words key) j).length) ≤ 303*(replicas key*s*w+W+replicas key)) →
      (∑ key ∈ keys, (physicalFamilyDispatchCost T A
        (inverseCallerWordWidth (Sizes.p n) key.1
          (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) key.2.1 (Sizes.s n i) (Sizes.t n i))
        (Sizes.p n) key.1
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
        key.2.2.1 key.2.2.2 key.2.1 (replicas key) work (words key) : ℝ)) ≤
      32000*(Sizes.T n : ℝ)+∑ key ∈ keys, (replicas key : ℝ)*D*(Sizes.t n i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n) key.1 : ℝ)^2/Sizes.d n)*
          (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hbatch⟩ := selectedRawFamilyKeyBatches_fast_le ct
  refine ⟨16000*D,mul_nonneg (by positivity) hD,?_⟩
  filter_upwards [hbatch] with n hn
  intro h i _ T A keys replicas work words hband hstock
  have hsum := Finset.sum_le_sum (s := keys) (fun key hk =>
    show (physicalFamilyDispatchCost T A
      (inverseCallerWordWidth (Sizes.p n) key.1
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) key.2.1 (Sizes.s n i) (Sizes.t n i))
      (Sizes.p n) key.1 (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) (Sizes.t n i) key.2.2.1 key.2.2.2 key.2.1 (replicas key) work (words key) : ℝ) ≤
      16000*(familyInverseBatchCallerCost A
      (inverseCallerWordWidth (Sizes.p n) key.1
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) key.2.1 (Sizes.s n i) (Sizes.t n i))
      (Sizes.p n) key.1 (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) (Sizes.t n i) key.2.2.1 key.2.2.2 key.2.1 (replicas key) : ℝ) from by
        exact_mod_cast physicalFamilyDispatchCost_le work (words key) (hstock key hk))
  rw [← Finset.mul_sum] at hsum
  have hb := mul_le_mul_of_nonneg_left (hn h i A keys replicas hband) (by positivity : (0 : ℝ) ≤ 16000)
  apply (hsum.trans hb).trans_eq
  rw [mul_add,Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro key hk
    ring

end IntegerMultBounds.MathlibTM2.Cost
