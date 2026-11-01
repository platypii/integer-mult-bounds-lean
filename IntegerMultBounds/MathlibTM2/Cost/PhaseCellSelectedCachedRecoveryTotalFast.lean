module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedRecoveryFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedReplicaSharedSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryMaskInitialization
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedNumericalSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAxisDensity
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock

/-! The executed initialized recovery caller has a complete selected time estimate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedInitializedCachedReplicaRecovery_total_fast_le (ct ce : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ (target : ℕ) (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H target X),
      ∀ htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card,
      ∀ steps : ℕ, steps ≤ initializedCachedBatchedReplicaRecoveryTime H (B.problem htarget) →
      (steps : ℝ) ≤
        (2*Sizes.T n+24 : ℕ)+
        D*H.Fs.length*(H.t : ℝ)*(1+(H.band : ℝ)^2/Sizes.d n)*(H.p : ℝ)^(129/128 : ℝ) := by
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  obtain ⟨D,hD,hfast⟩ := selectedInitializedCachedReplicaRecovery_fast_le ct ce
  refine ⟨D,hD,?_⟩
  filter_upwards [hfast,selectedReplicaHaloSharedTime_volume_le 20 cw 20 cV 1] with n hf hs
  intro h i _ H hp ht hl hu htarget hrhs target X B htargetRecovery steps hn
  have hc := hf h i H hp ht hl hu htarget hrhs target X B htargetRecovery steps hn
  obtain ⟨hl',hr,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hlH : H.l ≤ 20*H.p := by simpa only [hl,hp] using hl'
  have hrH : 2^H.l ≤ 20*H.p := by simpa only [hl,hp] using hr
  have hwH : H.wordWidth ≤ cw*H.p := by
    simpa only [ReplicaHaloProblem.wordWidth,hl,hp,cw] using hw
  have hVw : H.metadataWidth ≤ (2*cw+426009)*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
  have hVp : H.metadataWidth ≤ cV*H.p := by
    calc
      _ ≤ (2*cw+426009)*H.wordWidth := hVw
      _ ≤ (2*cw+426009)*(cw*H.p) := Nat.mul_le_mul_left _ hwH
      _ = cV*H.p := by dsimp only [cV]; ring
  obtain ⟨_,_,hwJ,hVJ⟩ := B.problem_sizing htargetRecovery
  have hshared := hs h i (B.problem htargetRecovery) hp ht (by change H.u ≤ H.p; simpa only [hp] using hu)
    hlH (hwJ.trans_le hwH) hrH (hVJ.trans_le hVp)
  have hsharedR : (initializedReplicaHaloSharedTime (B.problem htargetRecovery) : ℝ) ≤ Sizes.T n := by
    exact_mod_cast (by simpa only [one_mul] using hshared)
  push_cast at hc hsharedR ⊢
  linarith only [hc,hsharedR]

end IntegerMultBounds.MathlibTM2.Cost
