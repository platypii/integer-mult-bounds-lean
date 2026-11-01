module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFirstCachedReplicaPass
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedCouplingLocalFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaCouplingRowsResources
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedReplicaCouplingLoopFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryGapFast

/-! The executed cached first pass has sparse-volume fast work per replica.
All geometry and coefficient construction occurs in one shared setup bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFirstCachedReplicaPass_local_fast_le (ct ce : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {n : ℕ} (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ steps : ℕ, steps ≤ firstCachedReplicaPassTime H →
      (steps : ℝ) ≤ (initializedReplicaHaloSharedTime H+cachedReplicaCouplingSharedTime H+24 : ℕ)+
        F*H.Fs.length*(replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  let K := (10*cV+57)*cw+41
  obtain ⟨D,hD,hrows⟩ := selectedInitializedReplicaCouplingRows_fast_le ct ce
  obtain ⟨E,hE,hcoupling⟩ := cachedReplicaCouplingTransition_local_fast_le cw cV
  refine ⟨D+E+K,by positivity,?_⟩
  intro n h i _ H hp ht hl hu htarget hrhs steps hn
  have hr := hrows h i H hp ht hl hu htarget hrhs (initializedReplicaCouplingRowsTime H) (le_refl _)
  obtain ⟨_,_,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hwH : H.wordWidth ≤ cw*H.p := by simpa only [ReplicaHaloProblem.wordWidth,hl,hp,cw] using hw
  have hVw : H.metadataWidth ≤ (2*cw+426009)*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
  have hVH : H.metadataWidth ≤ cV*H.p := by
    calc
      _ ≤ (2*cw+426009)*H.wordWidth := hVw
      _ ≤ (2*cw+426009)*(cw*H.p) := Nat.mul_le_mul_left _ hwH
      _ = cV*H.p := by dsimp only [cV]; ring
  let G := replicaRecoveryLocalVolume H
  obtain ⟨_,hrowsG,_,_⟩ := replicaRecoveryLocalVolume_bounds H
  have hspan : H.span ≤ G := by dsimp only [G]; omega
  have hcard : (haloInterior (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card ≤ G := by
    unfold G replicaRecoveryLocalVolume replicaHaloLocalCoordinates
    omega
  have hG : 1 ≤ G := by dsimp only [G]; omega
  have hGp : 1 ≤ G*H.p := Nat.mul_pos hG H.p_pos
  have hsw := Nat.mul_le_mul hspan hwH
  have hcw := Nat.mul_le_mul hcard hwH
  have hnative : 38*(H.span*H.wordWidth)+41+
      (10*cV+19)*((haloInterior (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) ≤ K*G*H.p := by
    dsimp only [K]
    nlinarith only [hsw,hGp,Nat.mul_le_mul_left (10*cV+19) hcw]
  have hnR : ((H.Fs.length*(38*(H.span*H.wordWidth)+41)+
      (10*cV+19)*H.Fs.length*((haloInterior (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ) : ℝ) ≤
      ((K*H.Fs.length*G*H.p : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith only [Nat.mul_le_mul_left H.Fs.length hnative] : _ ≤ K*H.Fs.length*G*H.p)
  have hp1 : (1 : ℝ) ≤ H.p := by exact_mod_cast H.p_pos
  have hpow := mul_le_mul_of_nonneg_left
    (Real.self_le_rpow_of_one_le hp1 (by norm_num : (1 : ℝ) ≤ 129/128))
    (by positivity : (0 : ℝ) ≤ (K : ℝ)*H.Fs.length*G)
  have hc := mul_le_mul_of_nonneg_left (hcoupling H hwH hVH)
    (Nat.cast_nonneg H.Fs.length : (0 : ℝ) ≤ H.Fs.length)
  have hcoords : (replicaHaloLocalCoordinates H : ℝ) ≤ G := by
    have hh : replicaHaloLocalCoordinates H ≤ G := by unfold G replicaRecoveryLocalVolume; omega
    exact_mod_cast hh
  have hd := mul_le_mul_of_nonneg_left hcoords
    (by positivity : (0 : ℝ) ≤ D*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  have hs : (steps : ℝ) ≤ initializedReplicaCouplingRowsTime H+cachedReplicaCouplingSharedTime H+
      H.Fs.length*(cachedReplicaCouplingTransitionCost H H.metadataWidth+3 : ℕ)+4*H.Fs.length+6 := by
    exact_mod_cast (by rwa [firstCachedReplicaPassTime_split] at hn : steps ≤ _)
  change (initializedReplicaCouplingRowsTime H : ℝ) ≤
    ((initializedReplicaHaloSharedTime H+18+H.Fs.length*(38*(H.span*H.wordWidth)+37)+
      (10*cV+19)*H.Fs.length*((haloInterior (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ) : ℝ)+
      D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) at hr
  dsimp only [G] at hnR hpow hd
  push_cast at hr hnR hpow hc hd hs ⊢
  nlinarith only [hr,hnR,hpow,hc,hd,hs]

end IntegerMultBounds.MathlibTM2.Cost
