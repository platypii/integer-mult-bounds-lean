module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicRecoveryCouplingFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicFirstPassFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedResidualBatchFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCyclicBoundaryLedger
import Mathlib.Tactic.Linarith

/-! Compose the actual cached boundary caller. Setup remains explicit, and each
numerical replica term retains its own volume for subsequent amortization. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedCachedCyclicRecovery_fast_le (ct ce cw cV : ℕ) :
    ∃ F C D : ℝ, 0 ≤ F ∧ 0 ≤ C ∧ 0 ≤ D ∧
    ∀ {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (H K : ReplicaHaloProblem (Sizes.s n i))
      (u a span target q N W replicas : ℕ),
      H.p = Sizes.p n → K.p = Sizes.p n →
      H.t = Sizes.t n i → K.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      K.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → K.u ≤ Sizes.p n →
      H.target ≤ ct*Sizes.p n → K.target ≤ ct*Sizes.p n →
      H.rhsExp ≤ ce*Sizes.p n → K.rhsExp ≤ ce*Sizes.p n →
      H.Fs.length = replicas → K.Fs.length = replicas →
      H.wordWidth = 2*q+8 → K.wordWidth = 2*q+8 →
      H.metadataWidth ≤ cV*Sizes.p n → K.metadataWidth ≤ cV*Sizes.p n →
      H.span+K.span ≤ span → 1 ≤ Sizes.p n → 2*q+8 ≤ cw*Sizes.p n → 1 ≤ W →
      (cachedCyclicReplicaBoundaryBill H K (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i)
        a span target q (2*q+8) N W replicas+
        solvedCyclicRecoveryCost H K replicas N span (2*q+8) : ℕ) ≤
      (initializedReplicaHaloSharedTime H+cachedReplicaCouplingSharedTime H+24 : ℕ)+
      (initializedReplicaHaloSharedTime K+cachedReplicaCouplingSharedTime K+24 : ℕ)+
      (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K : ℕ)+
      (constructedCyclicFactorCost (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i)
        (Sizes.t n i) a span target 2 : ℕ)+
      (N*(6*(2*q+8)+9)+16 : ℕ)+
      F*replicas*(replicaRecoveryLocalVolume H : ℝ)*
        (Sizes.p n : ℝ)^(129/128 : ℝ)+
      F*replicas*(replicaRecoveryLocalVolume K : ℝ)*
        (Sizes.p n : ℝ)^(129/128 : ℝ)+
      replicas*(C*((N+1 : ℕ) : ℝ)*(W : ℝ)*(Sizes.p n : ℝ)^(129/128 : ℝ)+
        (22*N*(2*q+8)+25 : ℕ))+
      (200*(replicas+1)*(span+N+1)*(2*q+8+1) : ℕ)+
      (solvedCyclicRecoverySharedTime H K : ℝ)+
      replicas*(D*((replicaRecoveryLocalVolume H : ℝ)*(Sizes.p n : ℝ)^(129/128 : ℝ)+
        (replicaRecoveryLocalVolume K : ℝ)*(Sizes.p n : ℝ)^(129/128 : ℝ))+
        300*((N+span+1 : ℕ) : ℝ)*((2*q+8 : ℕ)+1)) := by
  obtain ⟨F,hF,hfirst⟩ := selectedCachedReplicaPass_local_fast_le ct ce
  obtain ⟨C,hC,hbatch⟩ := preparedResidualBatch_fast_le cw
  obtain ⟨D,hD,hrecovery⟩ := solvedCyclicRecovery_steps_local_fast_le cw cV
  refine ⟨F,C,D,hF,hC,hD,?_⟩
  intro n h i _ H K u a span target q N W replicas hpH hpK htH htK hlH hlK
    huH huK htargetH htargetK hrhsH hrhsK hH hK hwH hwK hVH hVK hspan hp hw hW
  have hfirstH := hfirst h i H hpH htH hlH huH htargetH hrhsH _ (le_refl _)
  have hfirstK := hfirst h i K hpK htK hlK huK htargetK hrhsK _ (le_refl _)
  rw [hH,hpH] at hfirstH
  rw [hK,hpK] at hfirstK
  have hb := hbatch (Sizes.p n) q N W replicas hp hw hW
  have hc := cachedCyclicReplicaBoundaryBill_le_components H K (Sizes.p n) u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.t n i)
    a span target q (2*q+8) N W replicas hH hK hwH hwK hspan
  have hwH' : H.wordWidth ≤ cw*H.p := by simpa only [hwH,hpH] using hw
  have hwK' : K.wordWidth ≤ cw*K.p := by simpa only [hwK,hpK] using hw
  have hVH' : H.metadataWidth ≤ cV*H.p := by simpa only [hpH] using hVH
  have hVK' : K.metadataWidth ≤ cV*K.p := by simpa only [hpK] using hVK
  have hr := hrecovery H K replicas N span (2*q+8) hH hK hwH hwK hspan
    hwH' hVH' hwK' hVK' _ (le_refl _)
  rw [hpH,hpK] at hr
  have hcR := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcR hfirstH hfirstK hb hr ⊢
  linarith

end IntegerMultBounds.MathlibTM2.Cost
