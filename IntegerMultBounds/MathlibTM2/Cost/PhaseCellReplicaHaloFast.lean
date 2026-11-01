module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedHaloReplicaResources
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReplicaHaloLoop

/-! The executed key body retains the fast arithmetic exponent. Shared page and
factory work stays explicit; replicated header traffic is linear in local volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def releasedReplicaSharedTime (p l B V span L s t u target rhsExp : ℕ) :=
  let w := executionWidth p l target rhsExp
  generateReplicaWeightPageCost 0 (2^15*p) s t u (executionPrecision p l target rhsExp) L w B+
    cachedBatchFromOriginsCost p l 0 L s t u target rhsExp+
    accumulatingGatheredPublicationCost 0 V span L w B+
    500*B*L*w+(preparedOriginAdvanceCost V span w B+2*(span*w)+2*B+10)+39

def generatedHaloReplicaSharedTime (p l V origin span L s t u target rhsExp : ℕ) :=
  let band := PhaseCellBand.width p u
  let B := (haloLengthGroup s t band origin (origin+span) L).length
  preparedPairedLocalHaloClassCost V s t band origin (origin+span) L+
    releasePairedOriginPagesCost B V+replicaClassReloadCost p l 0 B L s t u target rhsExp+
    releasedReplicaSharedTime p l B V span L s t u target rhsExp

theorem generatedHaloReplicaClass_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p l N V origin span L s t u target rhsExp : ℕ,
      1 ≤ p → 1 ≤ (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length →
      1 ≤ L → l ≤ cl*p → executionWidth p l target rhsExp ≤ cw*p → 2^l ≤ cr*p →
      weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionWidth p l target rhsExp) t u ≤ cV*p →
      let B := (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length
      (generatedHaloReplicaClassCost p l N V origin span L s t u target rhsExp : ℝ) ≤
        (generatedHaloReplicaSharedTime p l V origin span L s t u target rhsExp+
          (10*cV+19)*N*(B*L*executionWidth p l target rhsExp) : ℕ)+
        D*N*((B : ℝ)*((L : ℝ)+(2^l : ℕ))+span+1)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := releasedAccumulatingGatheredReplica_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro p l N V origin span L s t u target rhsExp hp hB hL hl hw hr hV
  dsimp only
  have hpw : p ≤ executionWidth p l target rhsExp := by
    unfold executionWidth executionExponent inputExponent
    omega
  have hVw := hV.trans (Nat.mul_le_mul_left cV hpw)
  have hc := generatedHaloReplicaClassCost_le_shared p l N V origin span L s t u target rhsExp cV hB hL hVw
  have hf := hfast p l N _ V span L s t u target rhsExp hp hB hL hl hw hr hV
  have hcR : (generatedHaloReplicaClassCost p l N V origin span L s t u target rhsExp : ℝ) ≤
      (preparedPairedLocalHaloClassCost V s t (PhaseCellBand.width p u) origin (origin+span) L+
        releasePairedOriginPagesCost (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length V+
        replicaClassReloadCost p l 0 (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length L s t u target rhsExp+
        releasedAccumulatingGatheredReplicaCost p l N (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length V span L s t u target rhsExp+
        (10*cV+19)*N*((haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length*L*executionWidth p l target rhsExp) : ℕ) := by
    exact_mod_cast hc
  unfold generatedHaloReplicaSharedTime releasedReplicaSharedTime
  dsimp only
  push_cast at hcR hf ⊢
  linarith only [hcR,hf]

def replicaHaloKeySharedTime {s : ℕ} (H : ReplicaHaloProblem s) (L : ℕ) :=
  replicaLengthKeyParserCost H.metadataWidth L+
    ((if H.offsets L = [] then
      preparedPairedLocalHaloClassCost H.metadataWidth s H.t H.band H.origin (H.origin+H.span) L+23
    else generatedHaloReplicaSharedTime H.p H.l H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp+2)+
      (2*L+2))

theorem replicaHaloKey_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} (H : ReplicaHaloProblem s) (L : ℕ),
      0 < L → H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      let B := (haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length
      (H.keyCost L : ℝ) ≤
        (replicaHaloKeySharedTime H L+(10*cV+19)*H.Fs.length*(B*L*H.wordWidth) : ℕ)+
        D*H.Fs.length*((B : ℝ)*((L : ℝ)+(2^H.l : ℕ))+H.span+1)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := generatedHaloReplicaClass_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro s H L hL hl hw hr hV
  dsimp only
  by_cases hempty : H.offsets L = []
  · have hgroup : haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L = [] := by
      apply List.length_eq_zero_iff.mp
      have hh : (H.offsets L).length = 0 := by rw [hempty]; rfl
      simpa only [ReplicaHaloProblem.offsets,haloPackedOffsets_length] using hh
    have hcost : H.keyCost L = replicaHaloKeySharedTime H L := by
      unfold ReplicaHaloProblem.keyCost processGeneratedHaloReplicaKeyCost replicaHaloKeySharedTime
      rw [conditionalGeneratedHaloReplicaClassCost_empty _ _ _ _ _ _ _ _ _ _ _ _ hgroup]
      simp only [hempty,ite_true]
      rfl
    rw [hcost]
    simp only [hgroup,List.length_nil,Nat.zero_mul,Nat.mul_zero,Nat.add_zero]
    exact le_add_of_nonneg_right (by positivity)
  · have hB : 1 ≤ (haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length := by
      have hh := List.length_pos_iff_ne_nil.mpr hempty
      have hh' : 1 ≤ (H.offsets L).length := by omega
      simpa only [ReplicaHaloProblem.offsets,haloPackedOffsets_length] using hh'
    have hBne : (haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length ≠ 0 := by omega
    have hf := hfast H.p H.l H.Fs.length H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp
      H.p_pos hB hL hl hw hr hV
    change ((replicaLengthKeyParserCost H.metadataWidth L+
      (conditionalGeneratedHaloReplicaClassCost H.p H.l H.Fs.length H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp+(2*L+2)) : ℕ) : ℝ) ≤ _
    rw [conditionalGeneratedHaloReplicaClassCost_nonempty _ _ _ _ _ _ _ _ _ _ _ _ hBne]
    simp only [replicaHaloKeySharedTime,hempty,ite_false]
    simp only [ReplicaHaloProblem.band,ReplicaHaloProblem.wordWidth] at hf ⊢
    push_cast at hf ⊢
    linarith only [hf]

end IntegerMultBounds.MathlibTM2.Cost
