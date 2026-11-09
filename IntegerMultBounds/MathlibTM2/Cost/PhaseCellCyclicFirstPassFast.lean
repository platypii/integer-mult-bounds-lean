module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaPass
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaPassLocal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaPass

/-! Transfer the established first-pass estimate to the actual cached cyclic
caller. Its renamed bill is the same cost, with no new numerical analysis. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedReplicaPassCost_eq_first {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    cachedReplicaPassCost H = firstCachedReplicaPassTime H := by
  rfl

theorem selectedCachedReplicaPass_fast_le (ct ce : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {n : ℕ} (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (H : ReplicaHaloProblem (Sizes.s n i)),
      H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ steps : ℕ, steps ≤ cachedReplicaPassCost H →
      (steps : ℝ) ≤ (initializedReplicaHaloSharedTime H+cachedReplicaCouplingSharedTime H+24 : ℕ)+
        F*H.Fs.length*((H.t+(H.t-Sizes.s n i)*H.band^2 : ℕ) : ℝ)*
          (H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hfast⟩ := selectedFirstCachedReplicaPass_fast_le ct ce
  refine ⟨F,hF,?_⟩
  intro n h i _ H hp ht hl hu htarget hrhs steps hsteps
  rw [cachedReplicaPassCost_eq_first] at hsteps
  exact hfast h i H hp ht hl hu htarget hrhs steps hsteps

theorem selectedCachedReplicaPass_local_fast_le (ct ce : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {n : ℕ} (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (H : ReplicaHaloProblem (Sizes.s n i)),
      H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ steps : ℕ, steps ≤ cachedReplicaPassCost H →
      (steps : ℝ) ≤ (initializedReplicaHaloSharedTime H+cachedReplicaCouplingSharedTime H+24 : ℕ)+
        F*H.Fs.length*(replicaRecoveryLocalVolume H : ℝ)*
          (H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hfast⟩ := selectedFirstCachedReplicaPass_local_fast_le ct ce
  refine ⟨F,hF,?_⟩
  intro n h i _ H hp ht hl hu htarget hrhs steps hsteps
  rw [cachedReplicaPassCost_eq_first] at hsteps
  exact hfast h i H hp ht hl hu htarget hrhs steps hsteps

end IntegerMultBounds.MathlibTM2.Cost
