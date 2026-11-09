module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicFactory
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup

/-! Absorb the actual cyclic factory setup at its scheduled multiplicity.
Replicas never multiply this bill; repeated schedule entries still do. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem selectedCyclicFactorySchedule_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ (jobs : List ι) (u target : ℕ) (a span : ι → ℕ),
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      jobs.length ≤ 2*Sizes.t n i →
      (∀ j ∈ jobs, a j ≤ Sizes.s n i ∧ span j ≤ Sizes.s n i) →
      scale*(jobs.map (fun j => constructedCyclicFactorCost (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
        (a j) (span j) (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2)).sum ≤ Sizes.T n := by
  obtain ⟨C,hC,hfactory⟩ := selectedConstructedCyclicFactorCost_poly_le ct
  filter_upwards [hfactory,selectedDistinctCoreSetup_volume_le ⌈C⌉₊ 0 6 scale] with n hf hs
  intro ι h i _ jobs u target a span hu ht hb hcount hparams
  apply hs i jobs _ hcount
  intro j hj
  have hc := hf h i u target (a j) (span j) hu ht hb (hparams j hj).1 (hparams j hj).2
  have hceil := mul_le_mul_of_nonneg_right (Nat.le_ceil C)
    (by positivity : (0 : ℝ) ≤ (Sizes.t n i : ℝ)^6)
  have hn : constructedCyclicFactorCost (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
      (a j) (span j) (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 ≤ ⌈C⌉₊*(Sizes.t n i)^6 := by
    exact_mod_cast hc.trans hceil
  simpa only [pow_zero,Nat.mul_one] using hn

/-- The actual proper-core class derives both setup multiplicity and fitting
principal windows from its computed membership predicate. -/
theorem selectedCyclicCoreClassFactory_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target width radius L : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → 0 < width →
      scale*((coreGatherIndices (Sizes.s n i) width radius L).map (fun k =>
        constructedCyclicFactorCost (Sizes.p n) u
          (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i)
          (coreStart width k-radius) L (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2)).sum ≤ Sizes.T n := by
  filter_upwards [selectedCyclicFactorySchedule_volume_le ct scale] with n hs
  intro h i _ u target width radius L hu ht hb hw
  apply hs h i (coreGatherIndices (Sizes.s n i) width radius L) u target
    (fun k => coreStart width k-radius) (fun _ => L) hu ht hb
  · have hc := coreGatherIndices_length_le (Sizes.s n i) width radius L hw
    have hh := h.good.lt i
    omega
  · intro k hk
    obtain ⟨hl,hr,hlen⟩ := coreGatherIndices_spec (Sizes.s n i) width radius L k hk
    constructor <;> omega

end IntegerMultBounds.MathlibTM2.Cost
