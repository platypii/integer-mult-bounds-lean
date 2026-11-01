module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryNumericalFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingCost

/-! The executed interval's active rows inject into the existing ambient guard geometry. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem retainedCouplingActiveRows_le_boundary {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (band a b origin N : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s) :
    retainedCouplingActiveRows boundary s t band a b origin N ≤
      (haloBoundary s t (2*band) a b).card+4*band := by
  have hshift : retainedCouplingActiveRows boundary s t band a b origin N ≤
      ((Finset.range s).filter (fun j => couplingSkipAt boundary s t band a b j = false)).card := by
    apply Finset.card_le_card_of_injOn (fun j => origin+j)
    · intro j hj
      obtain ⟨hj,hflag⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hflag⟩
      have hj' := Finset.mem_range.mp hj
      change origin+j < s
      omega
    · intro j hj k hk he
      change origin+j = origin+k at he
      omega
  have hpart := Finset.card_filter_add_card_filter_not (s := Finset.range s)
    (fun j => couplingSkipAt boundary s t band a b j = true)
  have htrue := couplingGuard_true_count hst boundary band a b hb
  have hsum : (couplingZeroRows true s t band a b).card+
      ((Finset.range s).filter (fun j => couplingSkipAt boundary s t band a b j = false)).card = s := by
    simpa only [Bool.eq_false_iff,Finset.card_range,htrue] using hpart
  have hcomp : (Finset.univ \ couplingZeroRows true s t band a b).card =
      s-(couplingZeroRows true s t band a b).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  have hfull : s-(couplingZeroRows true s t band a b).card ≤
      (haloBoundary s t (2*band) a b).card+4*band := by
    rw [←hcomp]
    exact recovery_active_card_le_boundary band a b
  omega

theorem retainedCouplingActiveRows_le_geometry {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (band a b origin N : ℕ) (hb : b ≤ s) (hfit : origin+N ≤ s) :
    retainedCouplingActiveRows boundary s t band a b origin N ≤
      haloBoundaryCountBound s t (2*band) a b+4*band :=
  (retainedCouplingActiveRows_le_boundary hst boundary band a b origin N hb hfit).trans
    (Nat.add_le_add_right (haloBoundary_card_bound hst (2*band) a b) _)

theorem batchedReplicaRecovery_geometry_fast_le (cl cw cr cV : ℕ) :
    ∃ C D E : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ E ∧
      ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) (target : ℕ)
      (X : ℕ → ZMod s → ℝ) (B : ReplicaRecoveryBatch H target X)
      (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (batchedReplicaRecoveryTime H (B.problem htarget) : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+
          H.Fs.length*(replicaRecoveryPreparationNativeCost H+50*(H.span*H.wordWidth)+25*H.span+59)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth)+24 : ℕ)+
        (D*(replicaHaloLocalCoordinates H : ℕ)+
          C*((haloBoundaryCountBound s H.t H.band H.origin (H.origin+H.span)+1 : ℕ))*((12*H.band+1 : ℕ) : ℝ)+
          E*(haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band)*((H.band+1 : ℕ) : ℝ))*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,D,E,hC,hD,hE,hfast⟩ := batchedReplicaRecovery_numerical_fast_le cl cw cr cV
  refine ⟨C,D,E,hC,hD,hE,?_⟩
  intro s _ H target X B htarget hl hw hr hV hgap hring
  have hc := hfast H target X B htarget hl hw hr hV hgap hring
  have hactive := retainedCouplingActiveRows_le_geometry H.s_lt_t true H.band H.origin
    (H.origin+H.span) H.origin H.span H.span_fit H.span_fit
  have hboundary := haloBoundary_card_bound H.s_lt_t H.band H.origin (H.origin+H.span)
  have ha : (retainedCouplingActiveRows true s H.t H.band H.origin (H.origin+H.span) H.origin H.span : ℝ) ≤
      (haloBoundaryCountBound s H.t (2*H.band) H.origin (H.origin+H.span)+4*H.band : ℕ) := by exact_mod_cast hactive
  have hb : ((haloBoundary s H.t H.band H.origin (H.origin+H.span)).card : ℝ) ≤
      haloBoundaryCountBound s H.t H.band H.origin (H.origin+H.span) := by exact_mod_cast hboundary
  have hma := mul_le_mul_of_nonneg_left ha
    (by positivity : (0 : ℝ) ≤ E*(H.band+1)*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  have hmb := mul_le_mul_of_nonneg_left hb
    (by positivity : (0 : ℝ) ≤ C*(12*H.band+1)*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  push_cast at hc hma hmb ⊢
  nlinarith only [hc,hma,hmb]

end IntegerMultBounds.MathlibTM2.Cost
