module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFirstCachedReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeneratedReplicaFactory
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaRecoveryTotal
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaRecoveryWorkspace

/-! Complete physical per-core time and extra workspace, including generated
factors. The normalized RHS uses exponent two and a positive recovery target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedGeneratedFirstCachedRecovery_time_le (ct cH : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)) (target : ℕ),
      H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) → H.u ≤ Sizes.p n →
      target ≤ ct*Sizes.p n → H.target ≤ cH*Sizes.p n → H.rhsExp = 2 →
      ∀ (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H (target+1) X)
        htargetRecovery, ∀ steps : ℕ,
      steps ≤ generatedReplicaBoundaryFactoryCost H (target+1)+firstCachedReplicaRecoveryTime H (B.problem htargetRecovery) →
      (steps : ℝ) ≤ (6*Sizes.T n+48 : ℕ)+
        F*H.Fs.length*(H.t : ℝ)*(1+(H.band : ℝ)^2/Sizes.d n)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hcaller⟩ := selectedFirstCachedReplicaRecovery_total_fast_le cH 2
  refine ⟨F,hF,?_⟩
  filter_upwards [hcaller,selectedGeneratedReplicaBoundaryFactoryCost_scaled_volume_le ct 1] with n hc hf
  intro h i _ H target hp ht hl hu htarget hHtarget hrhs X B hsetup steps hn
  have hrhsBound : H.rhsExp ≤ 2*Sizes.p n := by have := h.thirteen_le_p; omega
  have hcall := hc h i H hp ht hl hu hHtarget hrhsBound (target+1) X B hsetup
    (firstCachedReplicaRecoveryTime H (B.problem hsetup)) le_rfl
  have hfactory : (generatedReplicaBoundaryFactoryCost H (target+1) : ℝ) ≤ Sizes.T n := by
    exact_mod_cast (by simpa only [one_mul] using hf h i H target hp ht hl hu htarget hrhs hsetup)
  have hsteps : (steps : ℝ) ≤ generatedReplicaBoundaryFactoryCost H (target+1)+
      firstCachedReplicaRecoveryTime H (B.problem hsetup) := by exact_mod_cast hn
  push_cast at hcall ⊢
  linarith

theorem selectedGeneratedFirstCachedRecoveryWorkspace_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c M R K ct cH : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)) (target : ℕ),
      H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) → H.u ≤ Sizes.p n →
      target ≤ ct*Sizes.p n → H.target ≤ cH*Sizes.p n → H.rhsExp = 2 →
      ∀ (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H (target+1) X)
        htargetRecovery,
      generatedFirstCachedReplicaRecoveryWorkspace H (B.problem htargetRecovery) (target+1) hR hQ push c M R K ≤
        10*Sizes.T n+C*H.Fs.length*H.t*H.p := by
  let cw := 16*20+8*cH+8*2+128
  let cV := 2*cw+426009
  let C := cw*(226+80*replicaHaloTrafficFactor (A := A) (U := U) hQ R cV)+82+
    preparedReplicaRecoveryArchivesPush (Q := Q) (A := A) (U := U)*(22*cw+19)
  refine ⟨C,?_⟩
  filter_upwards [selectedFirstCachedReplicaRecoveryWorkspace_le hQ push c M R K cH 2,
    selectedGeneratedReplicaBoundaryFactoryCost_scaled_volume_le ct
      (generatedReplicaBoundaryFactoryPush (A := A) (U := U) hR hQ)] with n hc hf
  intro h i _ H target hp ht hl hu htarget hHtarget hrhs X B hsetup
  have hrhsBound : H.rhsExp ≤ 2*Sizes.p n := by have := h.thirteen_le_p; omega
  have hcall := hc h i H hp ht hl hu hHtarget hrhsBound (target+1) X B hsetup
  have hfactory := hf h i H target hp ht hl hu htarget hrhs hsetup
  change firstCachedReplicaRecoveryWorkspace H (B.problem hsetup) hQ push c M R K ≤
    9*Sizes.T n+C*H.Fs.length*H.t*H.p at hcall
  unfold generatedFirstCachedReplicaRecoveryWorkspace
  omega

end IntegerMultBounds.MathlibTM2.Cost
