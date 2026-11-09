module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicSecondInteriorTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSecondInteriorBudget
import Mathlib.Tactic.Linarith

/-! Price the named executed second-interior allowance, including both erasures. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem replicaNativeCleanup_le_shared {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s) :
    replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) ≤ 10*cachedReplicaCouplingSharedTime H := by
  have hw : 1 ≤ H.wordWidth := by
    unfold ReplicaHaloProblem.wordWidth executionWidth
    omega
  have htop := (Schoenhage.Schedule.topN_facts hw).2.1
  unfold replicaCouplingNativeCleanupBound replicaCouplingNativeWordBound
    cachedReplicaCouplingSharedTime replicaCouplingHeaderCost
  omega

private theorem sum_named_budget_le {ι : Type} {s : ℕ} [NeZero s]
    (jobs : List ι) (H K J M : ι → ReplicaHaloProblem s) (p : ℕ) (target N : ι → ℕ)
    (hparams : ∀ k ∈ jobs, (J k).target = boundaryHaloRecoveryTarget p (target k) (N k) ∧
      (M k).target = boundaryHaloRecoveryTarget p (target k) (N k) ∧
      (J k).rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p (H k).u) ∧
      (M k).rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p (H k).u)) :
    (jobs.map (fun k => cyclicSecondInteriorTimeBudget (H k) (K k) p (target k) (N k))).sum ≤
      (jobs.map (fun k => (H k).interiorTimeBudget (J k).target (J k).rhsExp+
        (K k).interiorTimeBudget (M k).target (M k).rhsExp)).sum+
      10*((jobs.map (fun k => cachedReplicaCouplingSharedTime (H k))).sum+
        (jobs.map (fun k => cachedReplicaCouplingSharedTime (K k))).sum) := by
  induction jobs with
  | nil => simp
  | cons k jobs ih =>
    obtain ⟨htJ,htM,heJ,heM⟩ := hparams k (by simp)
    have hcH := replicaNativeCleanup_le_shared (H k)
    have hcK := replicaNativeCleanup_le_shared (K k)
    have hs := ih (by intro x hx; exact hparams x (by simp [hx]))
    have hb : cyclicSecondInteriorTimeBudget (H k) (K k) p (target k) (N k) ≤
        (H k).interiorTimeBudget (J k).target (J k).rhsExp+
        (K k).interiorTimeBudget (M k).target (M k).rhsExp+
        10*(cachedReplicaCouplingSharedTime (H k)+cachedReplicaCouplingSharedTime (K k)) := by
      rw [htJ,htM,heJ,heM]
      unfold cyclicSecondInteriorTimeBudget
      dsimp only
      nlinarith only [hcH,hcK]
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hb,hs]

theorem selectedFittingCyclicSecondInteriorBudget_time_le (cl cw cr cV : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)],
      let s := Sizes.s n i
      let t := Sizes.t n i
      let p := Sizes.p n
      ∀ width band depth L replicas : ℕ, 0 < width → width ≤ s →
      depth*band ≤ width → 1 ≤ band → s/(t-s)+1 ≤ width → p^2+band^2 ≤ width →
      ∀ H K J M : ℕ → ReplicaHaloProblem s,
      (∀ k ∈ coreGatherIndices s width (depth*band) L,
        (H k).p = p ∧ (H k).t = t ∧ (H k).band = band ∧
        (H k).origin = coreStart width k-depth*band ∧
        (H k).span = min L (s-(coreStart width k-depth*band)) ∧
        (K k).p = p ∧ (K k).t = t ∧ (K k).band = band ∧
        (K k).span = L-min L (s-(coreStart width k-depth*band))) →
      (∀ k ∈ coreGatherIndices s width (depth*band) L,
        (H k).SameLayout (J k) ∧ (K k).SameLayout (M k)) →
      (∀ k ∈ coreGatherIndices s width (depth*band) L, ∀ R ∈ [H k,K k],
        R.Fs.length = replicas ∧ R.u ≤ R.p ∧ R.l ≤ cl*R.p ∧ R.wordWidth ≤ cw*R.p ∧
        2^R.l ≤ cr*R.p ∧ R.metadataWidth ≤ cV*R.p ∧ R.l = haloInverseRingLog s R.t) →
      ∀ target N : ℕ → ℕ,
      (∀ k ∈ coreGatherIndices s width (depth*band) L,
        (J k).target = boundaryHaloRecoveryTarget p (target k) (N k) ∧
        (M k).target = boundaryHaloRecoveryTarget p (target k) (N k) ∧
        (J k).rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p (H k).u) ∧
        (M k).rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p (H k).u)) →
      let jobs := coreGatherIndices s width (depth*band) L
      ((jobs.map (fun k => cyclicSecondInteriorTimeBudget (H k) (K k) p (target k) (N k))).sum : ℝ) ≤
      2*(Sizes.T n : ℝ)+680*F*replicas*((s+(t-s)*band^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hsecond⟩ := selectedFittingCyclicSecondInterior_time_le cl cw cr cV
  refine ⟨F,hF,?_⟩
  filter_upwards [hsecond,selectedCachedCouplingSharedSchedule_volume_le cw cV 20] with n hn hc
  intro h i _
  dsimp only
  intro width band depth L replicas hw hwidth hguard hband hcell hprepare H K J M hgeom hlayout hparams target N htarget
  let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
  have hcount : jobs.length ≤ 2*Sizes.t n i := by
    have hh := coreGatherIndices_length_le (Sizes.s n i) width (depth*band) L hw
    have hst := h.good.lt i
    dsimp only [jobs]
    omega
  have hcH := hc h i jobs H hcount (by
    intro k hk
    obtain ⟨hp,ht,_,_,_,_,_,_,_⟩ := hgeom k hk
    obtain ⟨_,hu,_,hw,_,hV,_⟩ := hparams k hk (H k) (by simp)
    exact ⟨hp,ht,hw,hu,hV⟩)
  have hcK := hc h i jobs K hcount (by
    intro k hk
    obtain ⟨_,_,_,_,_,hp,ht,_,_⟩ := hgeom k hk
    obtain ⟨_,hu,_,hw,_,hV,_⟩ := hparams k hk (K k) (by simp)
    exact ⟨hp,ht,hw,hu,hV⟩)
  have hcleanup : 10*((jobs.map (fun k => cachedReplicaCouplingSharedTime (H k))).sum+
      (jobs.map (fun k => cachedReplicaCouplingSharedTime (K k))).sum) ≤ Sizes.T n := by
    omega
  have hbudget := sum_named_budget_le jobs H K J M (Sizes.p n) target N htarget
  have hi := hn h i width band depth L replicas hw hwidth hguard hband hcell hprepare H K J M hgeom hlayout hparams
  have hbR := (Nat.cast_le (α := ℝ)).mpr hbudget
  have hcR := (Nat.cast_le (α := ℝ)).mpr hcleanup
  dsimp only [jobs] at hbR hcR
  dsimp only at hi
  push_cast at hbR hcR hi ⊢
  nlinarith only [hbR,hcR,hi]

end IntegerMultBounds.MathlibTM2.Cost
