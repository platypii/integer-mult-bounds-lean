module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryRowFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCachedBatchedReplicaRecovery

/-! All repeated work in the executed cached recovery caller satisfies the fast gap-volume bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cachedBatchedReplicaRecoveryTime_affine {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (target : ℕ) (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X) htarget :
    cachedBatchedReplicaRecoveryTime H (B.problem htarget) = initializedReplicaHaloTime (B.problem htarget)+
      H.Fs.length*(cachedReplicaRecoveryPreparationRowCost H+40*(H.span*H.wordWidth)+25*H.span+50)+24 := by
  unfold cachedBatchedReplicaRecoveryTime
  rw [replicaRecoveryInteriorTime_affine H target X B htarget]
  unfold retainedPackedPublicationMergeCost
  ring

theorem cachedBatchedReplicaRecovery_fast_le (cl cw cr cV : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t → H.p^2 ≤ H.t →
      (cachedBatchedReplicaRecoveryTime H (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+24 : ℕ)+
        F*H.Fs.length*((H.t+(H.t-s)*H.band^2 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hrow⟩ := cachedReplicaRecoveryPreparationRow_fast_le cw cV
  obtain ⟨D,hD,hinterior⟩ := replicaRecoveryBatchInterior_fast_le cl cw cr cV
  let K := (10*cV+69)*cw+84
  refine ⟨C+40*D+K,by positivity,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring haxis
  let G := H.t+(H.t-s)*H.band^2
  have hi := hinterior H target X B htarget hl hw hr hV hgap hring
  have ht : (cachedBatchedReplicaRecoveryTime H (B.problem htarget) : ℝ) ≤
      (initializedReplicaHaloSharedTime (B.problem htarget)+
        H.Fs.length*(cachedReplicaRecoveryPreparationRowCost H+50*(H.span*H.wordWidth)+25*H.span+59)+
        (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+24 : ℕ)+
      D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
    rw [cachedBatchedReplicaRecoveryTime_affine H target X B htarget]
    push_cast at hi ⊢
    nlinarith only [hi]
  have hspan : H.span ≤ G := by have := H.span_fit; have := H.s_lt_t; dsimp only [G]; omega
  have hcard : (haloInterior s H.t H.band H.origin (H.origin+H.span)).card ≤ G := by
    have hc : (haloInterior s H.t H.band H.origin (H.origin+H.span)).card ≤ s := by
      simpa only [ZMod.card] using (haloInterior s H.t H.band H.origin (H.origin+H.span)).card_le_univ
    have := H.s_lt_t
    dsimp only [G]
    omega
  have hG : 1 ≤ G := by have := H.s_lt_t; dsimp only [G]; omega
  have hp := H.p_pos
  have hGp : 1 ≤ G*H.p := Nat.mul_pos hG hp
  have hsw := Nat.mul_le_mul hspan hw
  have hcw := Nat.mul_le_mul hcard hw
  have hs : H.span ≤ G*H.p := hspan.trans (Nat.le_mul_of_pos_right _ hp)
  have hnative : 50*(H.span*H.wordWidth)+25*H.span+59+
      (10*cV+19)*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) ≤ K*G*H.p := by
    dsimp only [K]
    nlinarith only [hsw,hs,hGp,Nat.mul_le_mul_left (10*cV+19) hcw]
  have hn := Nat.mul_le_mul_left H.Fs.length hnative
  have hnR : ((H.Fs.length*(50*(H.span*H.wordWidth)+25*H.span+59)+
      (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ) : ℝ) ≤
      ((K*H.Fs.length*G*H.p : ℕ) : ℝ) := by exact_mod_cast (by nlinarith only [hn] : _ ≤ K*H.Fs.length*G*H.p)
  have hp1 : (1 : ℝ) ≤ H.p := by exact_mod_cast hp
  have hpow := mul_le_mul_of_nonneg_left
    (Real.self_le_rpow_of_one_le hp1 (by norm_num : (1 : ℝ) ≤ 129/128))
    (by positivity : (0 : ℝ) ≤ (K : ℝ)*H.Fs.length*G)
  have hb := mul_le_mul_of_nonneg_left (hrow H hw hV haxis)
    (Nat.cast_nonneg H.Fs.length : (0 : ℝ) ≤ H.Fs.length)
  have hcoords : (replicaHaloLocalCoordinates H : ℝ) ≤ (40*G : ℕ) := by
    exact_mod_cast (replicaHaloLocalCoordinates_le H).trans
      (Nat.mul_le_mul_left 40 (Nat.le_add_right H.t _))
  have hd := mul_le_mul_of_nonneg_left hcoords
    (by positivity : (0 : ℝ) ≤ D*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  dsimp only [G] at hnR hpow hd
  push_cast at ht hnR hpow hb hd ⊢
  nlinarith only [ht,hnR,hpow,hb,hd]

end IntegerMultBounds.MathlibTM2.Cost
