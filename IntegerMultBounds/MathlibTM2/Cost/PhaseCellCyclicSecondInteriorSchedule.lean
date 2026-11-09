module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaInteriorLayoutLocalFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicEmptyRecoveryVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryResourceBudgets
import Mathlib.Tactic.Linarith

/-! Both actual second-interior budgets share the fitting local-volume bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_local_le {ι : Type} (jobs : List ι) (cost shared volume : ι → ℕ)
    (A : ℝ) (h : ∀ j ∈ jobs, (cost j : ℝ) ≤ shared j+A*(volume j : ℝ)) :
    ((jobs.map cost).sum : ℝ) ≤ (jobs.map shared).sum+A*((jobs.map volume).sum : ℝ) := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hj := h j (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    nlinarith only [hj,hs]

theorem computedFittingCyclicSecondInteriorSchedule_fast_le (cl cw cr cV : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {s t : ℕ} [NeZero s], s < t → t-s ≤ s →
      ∀ p width band depth L replicas : ℕ, 0 < width → width ≤ s →
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
        R.Fs.length = replicas ∧ R.l ≤ cl*R.p ∧ R.wordWidth ≤ cw*R.p ∧
        2^R.l ≤ cr*R.p ∧ R.metadataWidth ≤ cV*R.p ∧ R.l = haloInverseRingLog s R.t) →
      let jobs := coreGatherIndices s width (depth*band) L
      ((jobs.map (fun k => (H k).interiorTimeBudget (J k).target (J k).rhsExp+
        (K k).interiorTimeBudget (M k).target (M k).rhsExp)).sum : ℝ) ≤
      (jobs.map (fun k => initializedReplicaHaloSharedTime (J k)+
        initializedReplicaHaloSharedTime (M k)+36)).sum+
      680*F*replicas*((s+(t-s)*band^2 : ℕ) : ℝ)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hfast⟩ := replicaRecoveryInterior_layout_local_fast_le cl cw cr cV
  refine ⟨F,hF,?_⟩
  intro s t _ hst hgap p width band depth L replicas hw hwidth hguard hband hcell hprepare H K J M
    hgeom hlayout hparams
  dsimp only
  let jobs := coreGatherIndices s width (depth*band) L
  have hs := sum_local_le jobs
    (fun k => (H k).interiorTimeBudget (J k).target (J k).rhsExp+
      (K k).interiorTimeBudget (M k).target (M k).rhsExp)
    (fun k => initializedReplicaHaloSharedTime (J k)+initializedReplicaHaloSharedTime (M k)+36)
    (fun k => replicaRecoveryLocalVolume (H k)+replicaRecoveryLocalVolume (K k))
    (F*replicas*(p : ℝ)^(129/128 : ℝ)) (by
      intro k hk
      obtain ⟨hpH,htH,_,_,_,hpK,htK,_,_⟩ := hgeom k hk
      obtain ⟨layoutH,layoutK⟩ := hlayout k hk
      obtain ⟨hH,hlH,hwH,hrH,hVH,hringH⟩ := hparams k hk (H k) (by simp)
      obtain ⟨hK,hlK,hwK,hrK,hVK,hringK⟩ := hparams k hk (K k) (by simp)
      have hleft := hfast (H k) (J k) layoutH hlH hwH hrH hVH
        (by simpa only [htH] using hgap) hringH
      have hright := hfast (K k) (M k) layoutK hlK hwK hrK hVK
        (by simpa only [htK] using hgap) hringK
      rw [hH,hpH] at hleft
      rw [hK,hpK] at hright
      rw [←layoutH.interiorTime_eq_budget,←layoutK.interiorTime_eq_budget]
      push_cast at hleft hright ⊢
      nlinarith only [hleft,hright])
  have hv := (Nat.cast_le (α := ℝ)).mpr
    (computedFittingCyclicRecoveryLocalVolume_sum_le hst p width band depth L
      hw hwidth hguard hband hcell hprepare H K hgeom)
  have hm := mul_le_mul_of_nonneg_left hv
    (by positivity : (0 : ℝ) ≤ F*replicas*(p : ℝ)^(129/128 : ℝ))
  dsimp only [jobs] at hs hm
  push_cast at hs hm ⊢
  nlinarith only [hs,hm]

end IntegerMultBounds.MathlibTM2.Cost
