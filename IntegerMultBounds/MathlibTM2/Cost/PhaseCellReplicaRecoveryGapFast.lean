module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryGeometryFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyKernelVolume

/-! Actual recovery numerical work fits the existing phase-gap volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem replicaHaloLocalCoordinates_le {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    replicaHaloLocalCoordinates H ≤ 40*H.t := by
  have hs := H.s_lt_t
  have hspan := H.span_fit
  have hcard : (haloInterior s H.t H.band H.origin (H.origin+H.span)).card ≤ s := by
    simpa only [ZMod.card] using (haloInterior s H.t H.band H.origin (H.origin+H.span)).card_le_univ
  have hdiv := Nat.div_le_self s (H.t-s)
  unfold replicaHaloLocalCoordinates
  omega

theorem batchedReplicaRecovery_gap_fast_le (cl cw cr cV : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (batchedReplicaRecoveryTime H (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+
          H.Fs.length*(replicaRecoveryPreparationNativeCost H+50*(H.span*H.wordWidth)+25*H.span+59)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+24 : ℕ)+
        F*H.Fs.length*((H.t+(H.t-s)*H.band^2 : ℕ) : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,D,E,hC,hD,hE,hfast⟩ := batchedReplicaRecovery_numerical_fast_le cl cw cr cV
  refine ⟨40*D+200*C+200*E,by positivity,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring
  have hc := hfast H target X B htarget hl hw hr hV hgap hring
  have hv := familyKernelVolume_le (a := H.origin) (b := H.origin+H.span) H.s_lt_t
    (PhaseCellBand.width_pos H.p H.u)
  have hb : ((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*(12*H.band+1) ≤
      familyKernelVolume s H.t H.band H.origin (H.origin+H.span) := by
    unfold familyKernelVolume
    omega
  have hactive := retainedCouplingActiveRows_le_geometry H.s_lt_t true H.band H.origin
    (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have ha : retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span) H.origin H.span*(H.band+1) ≤
      familyKernelVolume s H.t H.band H.origin (H.origin+H.span) := by
    calc
      _ ≤ (haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*(2*H.band+1) :=
        Nat.mul_le_mul hactive (by omega)
      _ ≤ _ := by unfold familyKernelVolume; omega
  have hbR : (((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card+1)*(12*H.band+1) : ℕ) ≤
      ((200*(H.t+(H.t-s)*H.band^2) : ℕ) : ℝ) := by exact_mod_cast hb.trans hv
  have haR : (retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span) H.origin H.span*(H.band+1) : ℕ) ≤
      ((200*(H.t+(H.t-s)*H.band^2) : ℕ) : ℝ) := by exact_mod_cast ha.trans hv
  have hdR : (replicaHaloLocalCoordinates H : ℝ) ≤ (40*(H.t+(H.t-s)*H.band^2) : ℕ) := by
    exact_mod_cast (replicaHaloLocalCoordinates_le H).trans
      (Nat.mul_le_mul_left 40 (Nat.le_add_right H.t _))
  have hbs := mul_le_mul_of_nonneg_left hbR (by positivity : (0 : ℝ) ≤ C*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  have has := mul_le_mul_of_nonneg_left haR (by positivity : (0 : ℝ) ≤ E*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  have hds := mul_le_mul_of_nonneg_left hdR (by positivity : (0 : ℝ) ≤ D*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  push_cast at hc hbs has hds ⊢
  nlinarith only [hc,hbs,has,hds]

end IntegerMultBounds.MathlibTM2.Cost
