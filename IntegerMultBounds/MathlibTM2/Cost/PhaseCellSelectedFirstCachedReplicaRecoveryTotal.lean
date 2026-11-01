module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryHandoff
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaPassTotal
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedRecoveryTotalFast

/-! Complete time for the executed first-pass, handoff and recovery caller.
Shared setup is charged per core; distinct-core scheduling remains separate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFirstCachedReplicaRecovery_total_fast_le (ct ce : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ (target : ℕ) (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H target X),
      ∀ htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card,
      ∀ steps : ℕ, steps ≤ firstCachedReplicaRecoveryTime H (B.problem htarget) →
      (steps : ℝ) ≤ (5*Sizes.T n+48 : ℕ)+
        F*H.Fs.length*(H.t : ℝ)*(1+(H.band : ℝ)^2/Sizes.d n)*(H.p : ℝ)^(129/128 : ℝ) := by
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  let K := 22*cw+19
  obtain ⟨D,hD,hfirst⟩ := selectedFirstCachedReplicaPass_total_fast_le ct ce
  obtain ⟨E,hE,hrecovery⟩ := selectedInitializedCachedReplicaRecovery_total_fast_le ct ce
  refine ⟨D+E+K,by positivity,?_⟩
  filter_upwards [hfirst,hrecovery,selectedCachedReplicaCouplingSharedTime_volume_le cw cV 100] with n hf hr hh
  intro h i _ H hp ht hl hu htarget hrhs target X B htargetRecovery steps hn
  have hfirstH := hf h i H hp ht hl hu htarget hrhs (firstCachedReplicaPassTime H) (le_refl _)
  have hrecoveryH := hr h i H hp ht hl hu htarget hrhs target X B htargetRecovery
    (initializedCachedBatchedReplicaRecoveryTime H (B.problem htargetRecovery)) (le_refl _)
  obtain ⟨_,_,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hwH : H.wordWidth ≤ cw*H.p := by simpa only [ReplicaHaloProblem.wordWidth,hl,hp,cw] using hw
  have hVw : H.metadataWidth ≤ (2*cw+426009)*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
  have hVp : H.metadataWidth ≤ cV*H.p := by
    calc
      _ ≤ (2*cw+426009)*H.wordWidth := hVw
      _ ≤ (2*cw+426009)*(cw*H.p) := Nat.mul_le_mul_left _ hwH
      _ = cV*H.p := by dsimp only [cV]; ring
  have hshared := hh h i H hp ht hwH (by simpa only [hp] using hu) hVp
  have hhandoff : (cachedReplicaRecoveryHandoffSharedTime H : ℝ) ≤ Sizes.T n := by
    exact_mod_cast (cachedReplicaRecoveryHandoffSharedTime_le H).trans hshared
  have harchive := cachedReplicaRecoveryArchive_fast_le cw H hwH
  have hv := axisGapVolume_le (band := H.band)
    (by have := h.one_le_d; omega : 0 < Sizes.d n) (h.good.lt i).le (h.good.bounds i)
  rw [←ht] at hv
  have hgap := mul_le_mul_of_nonneg_left hv
    (by positivity : (0 : ℝ) ≤ (K : ℝ)*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  change _ ≤ (K : ℝ)*H.Fs.length*((H.t+(H.t-Sizes.s n i)*H.band^2 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) at harchive
  have hs : (steps : ℝ) ≤ firstCachedReplicaPassTime H+cachedReplicaRecoveryHandoffSharedTime H+
      H.Fs.length*(22*(H.span*H.wordWidth)+19 : ℕ)+initializedCachedBatchedReplicaRecoveryTime H (B.problem htargetRecovery) := by
    exact_mod_cast (by rwa [firstCachedReplicaRecoveryTime_split] at hn : steps ≤ _)
  push_cast at hfirstH hrecoveryH hhandoff harchive hgap hs ⊢
  nlinarith only [hfirstH,hrecoveryH,hhandoff,harchive,hgap,hs]

end IntegerMultBounds.MathlibTM2.Cost
