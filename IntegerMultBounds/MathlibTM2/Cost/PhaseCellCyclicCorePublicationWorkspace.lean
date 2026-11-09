module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreArchiveStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedComponentStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSetupVolume

/-! Final core publication and component pairing use linear payload space.
The shared term is explicit so selected-size absorption can treat it separately. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cyclicCorePublicationWorkspace_le (radius core span W replicas complexCount : ℕ)
    (hspan : radius+core ≤ span) :
    normalizedCorePublicationWorkspace radius core W replicas+
      normalizedComponentSolutionsWorkspace core W complexCount ≤
        1300*(replicas+complexCount)*(span+1)*(W+1)+2600*(span+1)*(W+1) := by
  have harchive : normalizedCorePublicationWorkspace radius core W replicas ≤
      1300*(replicas+1)*(span+1)*(W+1) := by
    unfold normalizedCorePublicationWorkspace
    calc
      13*((replicas+1)*(radius+core+1)*(100*W+100)) =
          1300*(replicas+1)*(radius+core+1)*(W+1) := by ring
      _ ≤ 1300*(replicas+1)*(span+1)*(W+1) := by gcongr
  have hpair : normalizedComponentSolutionsWorkspace core W complexCount ≤
      1300*(complexCount+1)*(span+1)*(W+1) := by
    unfold normalizedComponentSolutionsWorkspace
    calc
      13*((complexCount+1)*(core+1)*(40*W+100)) ≤
          13*((complexCount+1)*(span+1)*(100*W+100)) := by gcongr <;> omega
      _ = 1300*(complexCount+1)*(span+1)*(W+1) := by ring
  calc
    _ ≤ 1300*(replicas+1)*(span+1)*(W+1)+1300*(complexCount+1)*(span+1)*(W+1) :=
      Nat.add_le_add harchive hpair
    _ = _ := by ring

/-- The shared tail allowance fits global volume; only linear replica payload remains. -/
theorem selectedCyclicCorePublicationWorkspace_le (cw : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ radius core span W replicas complexCount : ℕ,
      radius+core ≤ span → span ≤ Sizes.s n i → W ≤ cw*Sizes.p n →
      normalizedCorePublicationWorkspace radius core W replicas+
        normalizedComponentSolutionsWorkspace core W complexCount ≤
          1300*(replicas+complexCount)*(span+1)*(W+1)+Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume (5200*(cw+1)) 1 1] with n hv
  intro h i radius core span W replicas complexCount hcore hspan hW
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hs : span+1 ≤ 2*Sizes.t n i := by have := h.good.lt i; omega
  have hw : W+1 ≤ (cw+1)*Sizes.p n := by nlinarith only [hW,hp]
  have hshared := Nat.mul_le_mul_left 2600 (Nat.mul_le_mul hs hw)
  have hvolume := hv i
  simp only [pow_one] at hvolume
  have hsharedVolume : 2600*(span+1)*(W+1) ≤ Sizes.T n := by
    nlinarith only [hshared,hvolume]
  exact (cyclicCorePublicationWorkspace_le radius core span W replicas complexCount hcore).trans
    (Nat.add_le_add_left hsharedVolume _)

end IntegerMultBounds.MathlibTM2.Cost
