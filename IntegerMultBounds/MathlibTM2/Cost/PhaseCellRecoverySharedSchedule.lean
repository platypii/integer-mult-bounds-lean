module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedReplicaSharedSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCompleteCachedRecoveryLedger

/-! Sum the actual interior and mask setup bills before volume absorption. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- One volume reserve pays the interior setup of every distinct core.
The record type may depend on the selected axis. -/
theorem selectedReplicaHaloSharedSchedule_volume_le (cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {α : Type} (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (records : List α) (H : α → ReplicaHaloProblem (Sizes.s n i)),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, (H r).p = Sizes.p n ∧ (H r).t = Sizes.t n i ∧
        (H r).u ≤ (H r).p ∧ (H r).l ≤ cl*(H r).p ∧
        (H r).wordWidth ≤ cw*(H r).p ∧ 2^(H r).l ≤ cr*(H r).p ∧
        (H r).metadataWidth ≤ cV*(H r).p) →
      scale*(records.map (fun r => initializedReplicaHaloSharedTime (H r))).sum ≤ Sizes.T n := by
  let C := ((6*(1000000*(ssMulConst+1)+8*mtCvKf 10+4100000)+400000)*64^6)*
    (32768+cl+cw+cr+cV+10)^12
  filter_upwards [selectedDistinctCoreSetup_volume_le C 12 12 scale] with n hs
  intro α i _ records H hcount hparams
  apply hs i records (fun r => initializedReplicaHaloSharedTime (H r)) hcount
  intro r hr
  obtain ⟨hp,ht,hu,hl,hw,hpow,hV⟩ := hparams r hr
  have hc := initializedReplicaHaloSharedTime_axis_poly_le cl cw cr cV (H r) hu hl hw hpow hV
  simpa only [hp,ht] using hc

/-- Recovery-mask generation is also shared over the whole core schedule. -/
theorem selectedRecoveryMasksSchedule_volume_le (cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {α : Type} (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      (records : List α) (V span band : α → ℕ), records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, span r ≤ Sizes.t n i ∧ band r ≤ Sizes.t n i ∧ V r ≤ cV*Sizes.p n) →
      scale*(records.map (fun r => initializeRecoveryMasksCost (V r) (span r) (band r))).sum ≤ Sizes.T n := by
  filter_upwards [selectedDistinctCoreSetup_volume_le (30000*(cV+5)^2) 4 6 scale] with n hs
  intro α h i records V span band hcount hparams
  apply hs i records (fun r => initializeRecoveryMasksCost (V r) (span r) (band r)) hcount
  intro r hr
  obtain ⟨hspan,hband,hV⟩ := hparams r hr
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  simpa only [Nat.mul_assoc] using initializeRecoveryMasksCost_core_le cV hspan hband ht hp hV

theorem selectedCachedCouplingSharedSchedule_volume_le (cw cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {α : Type} (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (records : List α) (H : α → ReplicaHaloProblem (Sizes.s n i)),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, (H r).p = Sizes.p n ∧ (H r).t = Sizes.t n i ∧
        (H r).wordWidth ≤ cw*(H r).p ∧ (H r).u ≤ (H r).p ∧
        (H r).metadataWidth ≤ cV*(H r).p) →
      scale*(records.map (fun r => cachedReplicaCouplingSharedTime (H r))).sum ≤ Sizes.T n := by
  let C := 20000000*(2*cw+cV+500000)^5
  filter_upwards [selectedDistinctCoreSetup_volume_le C 5 5 scale] with n hs
  intro α h i _ records H hcount hparams
  apply hs i records (fun r => cachedReplicaCouplingSharedTime (H r)) hcount
  intro r hr
  obtain ⟨hp,ht,hw,hu,hV⟩ := hparams r hr
  have hc := selectedCachedReplicaCouplingSharedTime_poly_le cw cV h i (H r) hp ht hw hu hV
  have heq (a b c d : ℕ) : a*(b*c*d)^5 = (a*b^5)*c^5*d^5 := by ring
  rw [heq,hp,ht] at hc
  exact hc

private theorem completeSharedSchedule_le {α : Type} {s : ℕ} [NeZero s]
    (records : List α) (H J : α → ReplicaHaloProblem s) :
    (records.map (fun r => completeCachedRecoverySharedTime (H r) (J r))).sum ≤
      (records.map (fun r => initializedReplicaHaloSharedTime (H r))).sum+
      (records.map (fun r => initializedReplicaHaloSharedTime (J r))).sum+
      101*(records.map (fun r => cachedReplicaCouplingSharedTime (H r))).sum+
      (records.map (fun r => initializeRecoveryMasksCost (H r).metadataWidth (H r).span (H r).band)).sum+
      48*records.length := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hh := cachedReplicaRecoveryHandoffSharedTime_le (H r)
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [completeCachedRecoverySharedTime]
    nlinarith only [ih,hh]

/-- All shared work of the complete caller, including both interiors, handoff
and masks, fits a single reserve after summing the distinct-core schedule. -/
theorem selectedCompleteCachedRecoverySharedSchedule_volume_le (cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {α : Type} (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (records : List α) (H J : α → ReplicaHaloProblem (Sizes.s n i)),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, ∀ G ∈ [H r,J r], G.p = Sizes.p n ∧ G.t = Sizes.t n i ∧
        G.u ≤ G.p ∧ G.l ≤ cl*G.p ∧ G.wordWidth ≤ cw*G.p ∧
        2^G.l ≤ cr*G.p ∧ G.metadataWidth ≤ cV*G.p) →
      scale*(records.map (fun r => completeCachedRecoverySharedTime (H r) (J r))).sum ≤ Sizes.T n := by
  filter_upwards [selectedReplicaHaloSharedSchedule_volume_le cl cw cr cV (5*scale),
    selectedCachedCouplingSharedSchedule_volume_le cw cV (505*scale),
    selectedRecoveryMasksSchedule_volume_le cV (5*scale),
    selectedDistinctCoreSetup_volume_le 48 0 0 (5*scale)] with n hinterior hcoupling hmasks hconstant
  intro α h i _ records H J hcount hparams
  have hH r hr := hparams r hr (H r) (by simp)
  have hJ r hr := hparams r hr (J r) (by simp)
  have hfirst := hinterior i records H hcount hH
  have hsecond := hinterior i records J hcount hJ
  have hc := hcoupling h i records H hcount (by
    intro r hr
    obtain ⟨hp,ht,hu,_,hw,_,hV⟩ := hH r hr
    exact ⟨hp,ht,hw,hu,hV⟩)
  have hm := hmasks h i records (fun r => (H r).metadataWidth) (fun r => (H r).span)
    (fun r => (H r).band) hcount (by
      intro r hr
      obtain ⟨hp,ht,_,_,_,_,hV⟩ := hH r hr
      have hs := (H r).span_fit
      have hb : (H r).band ≤ Sizes.s n i := (H r).band_fit
      have hst := (H r).s_lt_t
      refine ⟨?_,?_,?_⟩
      · omega
      · omega
      · simpa only [hp] using hV)
  have hk := hconstant i records (fun _ => 48) hcount (by simp)
  have hk' : (5*scale)*(48*records.length) ≤ Sizes.T n := by
    have heq (xs : List α) : (xs.map (fun _ => 48)).sum = 48*xs.length := by
      induction xs with
      | nil => rfl
      | cons r records ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        omega
    rwa [heq records] at hk
  have hs := Nat.mul_le_mul_left scale (completeSharedSchedule_le records H J)
  nlinarith only [hfirst,hsecond,hc,hm,hk',hs]

/-- Raw jobs' recovery problems inherit the original numerical widths; callers
need supply a profile only for the original problems. -/
theorem selectedRawRecoveryCallerSharedSchedule_volume_le (cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (records : List (RawRecoveryJob (Sizes.s n i)))
      (B : ∀ r : RawRecoveryJob (Sizes.s n i), ReplicaRecoveryBatch r.problem r.target r.solution),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, r.problem.p = Sizes.p n ∧ r.problem.t = Sizes.t n i ∧
        r.problem.u ≤ r.problem.p ∧ r.problem.l ≤ cl*r.problem.p ∧
        r.problem.wordWidth ≤ cw*r.problem.p ∧ 2^r.problem.l ≤ cr*r.problem.p ∧
        r.problem.metadataWidth ≤ cV*r.problem.p) →
      scale*(records.map (fun r => completeCachedRecoverySharedTime r.problem
        ((B r).problem r.sizing))).sum ≤ Sizes.T n := by
  filter_upwards [selectedCompleteCachedRecoverySharedSchedule_volume_le cl cw cr cV scale] with n hs
  intro h i _ records B hcount hparams
  apply hs h i records (fun r => r.problem) (fun r => (B r).problem r.sizing) hcount
  intro r hr G hG
  rcases List.mem_cons.mp hG with hG | hG
  · subst G
    exact hparams r hr
  · have heq : G = (B r).problem r.sizing := by simpa only [List.mem_singleton] using hG
    subst G
    obtain ⟨hp,ht,hu,hl,hw,hpow,hV⟩ := hparams r hr
    obtain ⟨_,_,hword,hmeta⟩ := (B r).problem_sizing r.sizing
    refine ⟨hp,ht,hu,hl,?_,hpow,?_⟩
    · rw [hword]
      change r.problem.wordWidth ≤ cw*r.problem.p
      exact hw
    · rw [hmeta]
      change r.problem.metadataWidth ≤ cV*r.problem.p
      exact hV

end IntegerMultBounds.MathlibTM2.Cost
