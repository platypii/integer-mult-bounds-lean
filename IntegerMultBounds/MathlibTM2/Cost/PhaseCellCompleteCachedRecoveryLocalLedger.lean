module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCompleteCachedRecoveryLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaPassLocal
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryInputLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryHandoff

/-! Keep every shared bill explicit until the distinct-core schedule is summed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedReplicaRecoveryArchive_local_fast_le (cw : ℕ) {s : ℕ} [NeZero s]
    (H : ReplicaHaloProblem s) (hw : H.wordWidth ≤ cw*H.p) :
    ((H.Fs.length*(22*(H.span*H.wordWidth)+19) : ℕ) : ℝ) ≤
      (22*cw+19 : ℕ)*H.Fs.length*(replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  let G := replicaRecoveryLocalVolume H
  obtain ⟨_,hrows,_,_⟩ := replicaRecoveryLocalVolume_bounds H
  have hG : 1 ≤ G := by dsimp only [G]; omega
  have hspan : H.span ≤ G := by dsimp only [G]; omega
  have hp : 1 ≤ H.p := H.p_pos
  have hline := Nat.mul_le_mul hspan hw
  have hunit : 1 ≤ G*H.p := Nat.mul_pos hG hp
  have hn : H.Fs.length*(22*(H.span*H.wordWidth)+19) ≤ (22*cw+19)*H.Fs.length*G*H.p := by
    have hh : 22*(H.span*H.wordWidth)+19 ≤ (22*cw+19)*G*H.p := by nlinarith only [hline,hunit]
    nlinarith only [Nat.mul_le_mul_left H.Fs.length hh]
  have hnR : ((H.Fs.length*(22*(H.span*H.wordWidth)+19) : ℕ) : ℝ) ≤
      (22*cw+19 : ℕ)*H.Fs.length*G*H.p := by exact_mod_cast hn
  have hp1 : (1 : ℝ) ≤ H.p := by exact_mod_cast hp
  have hpow := mul_le_mul_of_nonneg_left
    (Real.self_le_rpow_of_one_le hp1 (by norm_num : (1 : ℝ) ≤ 129/128))
    (by positivity : (0 : ℝ) ≤ (22*cw+19 : ℕ)*H.Fs.length*G)
  exact hnR.trans hpow

theorem selectedCompleteCachedRecovery_local_ledger_le (ct ce : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {n : ℕ} (_h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ (target : ℕ) (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htargetRecovery : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card),
      (firstCachedReplicaRecoveryTime H (B.problem htargetRecovery) : ℝ) ≤
        completeCachedRecoverySharedTime H (B.problem htargetRecovery)+
        F*H.Fs.length*(replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  obtain ⟨D,hD,hfast⟩ := cachedBatchedReplicaRecovery_local_fast_le 20 cw 20 cV
  obtain ⟨E,hE,hfirst⟩ := selectedFirstCachedReplicaPass_local_fast_le ct ce
  refine ⟨E+D+(22*cw+19 : ℕ),by positivity,?_⟩
  intro n h i _ H hp ht hl hu htarget hrhs target X B htargetRecovery
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
  have hg : H.t-Sizes.s n i ≤ Sizes.s n i := by rw [ht]; exact selectedAxis_gap_le_source h i
  have hlRing : H.l = haloInverseRingLog (Sizes.s n i) H.t := by rw [ht]; exact hl
  have hc := hfast H target X B htargetRecovery hlH hwH hrH hVp hg hlRing
  have hf := hfirst h i H hp ht hl hu htarget hrhs _ (le_refl _)
  have ha := cachedReplicaRecoveryArchive_local_fast_le cw H hwH
  rw [firstCachedReplicaRecoveryTime_split]
  unfold initializedCachedBatchedReplicaRecoveryTime completeCachedRecoverySharedTime
  push_cast at hc hf ha ⊢
  nlinarith only [hc,hf,ha]

/-- The actual raw-job bill retains factory and normalization setup, while
normalization payload remains linear in the sum of halo spans. -/
theorem selectedRawRecoveryJob_local_ledger_le (ct ce : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {n : ℕ} (_h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (r : RawRecoveryJob (Sizes.s n i)), r.problem.p = Sizes.p n →
      r.problem.t = Sizes.t n i →
      r.problem.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      r.problem.u ≤ Sizes.p n → r.problem.target ≤ ct*Sizes.p n →
      r.problem.rhsExp ≤ ce*Sizes.p n →
      ∀ B : ReplicaRecoveryBatch r.problem r.target r.solution,
      (r.runTime B : ℝ) ≤
        (normalizeRecoveryInputSharedTime r.problem r.W+
          generatedReplicaBoundaryFactoryCost r.problem r.target+
          completeCachedRecoverySharedTime r.problem (B.problem r.sizing) : ℕ)+
        r.problem.Fs.length*(normalizeRecoveryInputRowTime r.problem r.W : ℝ)+
        F*r.problem.Fs.length*
          (replicaRecoveryLocalVolume r.problem : ℝ)*
          (r.problem.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hbound⟩ := selectedCompleteCachedRecovery_local_ledger_le ct ce
  refine ⟨F,hF,?_⟩
  intro n h i _ r hp ht hl hu htarget hrhs B
  have hc := hbound h i r.problem hp ht hl hu htarget hrhs r.target r.solution B r.sizing
  rw [rawRecoveryJob_runTime_split]
  push_cast at hc ⊢
  linarith only [hc]

end IntegerMultBounds.MathlibTM2.Cost
