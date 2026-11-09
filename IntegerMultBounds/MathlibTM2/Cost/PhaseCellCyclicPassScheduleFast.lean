module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicFirstPassFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicRecoveryCouplingFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicEmptyRecoveryVolume
public import IntegerMultBounds.NLogN.PhaseCellCoreGatherVolume
import Mathlib.Tactic.Linarith

/-! Sum the two cached first passes and solved recovery over the computed
fitting class. Shared work and native traffic retain their actual schedules. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_schedule_le {ι : Type} (jobs : List ι) (cost shared traffic volume : ι → ℕ)
    (A B : ℝ)
    (hcost : ∀ j ∈ jobs, (cost j : ℝ) ≤ shared j+A*(traffic j : ℝ)+B*(volume j : ℝ)) :
    ((jobs.map cost).sum : ℝ) ≤ (jobs.map shared).sum+
      A*((jobs.map traffic).sum : ℝ)+B*((jobs.map volume).sum : ℝ) := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hj := hcost j (by simp)
    have hs := ih (by intro x hx; exact hcost x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    nlinarith only [hj,hs]

private theorem sum_uniform_le {ι : Type} (jobs : List ι) (f : ι → ℕ) (B : ℕ)
    (h : ∀ j ∈ jobs, f j ≤ B) : (jobs.map f).sum ≤ jobs.length*B := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hj := h j (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hj,hs]

/-- Native traffic is linear in the actual gathered volume, even when widths
vary between calls. The caller supplies no schedule-volume estimate. -/
theorem computedFittingCyclicTraffic_sum_le (s width radius L p cw : ℕ)
    (hw : 0 < width) (hwidth : width ≤ s) (hradius : radius ≤ width)
    (N w : ℕ → ℕ)
    (hparams : ∀ k ∈ coreGatherIndices s width radius L, N k ≤ L ∧ w k ≤ cw*p) :
    ((coreGatherIndices s width radius L).map (fun k => (N k+L+1)*(w k+1))).sum ≤
      14*s*(cw*p+1) := by
  let jobs := coreGatherIndices s width radius L
  have hs := sum_uniform_le jobs (fun k => (N k+L+1)*(w k+1))
    ((2*L+1)*(cw*p+1)) (by
      intro k hk
      obtain ⟨hN,hw⟩ := hparams k hk
      exact Nat.mul_le_mul (by omega) (by omega))
  have hv := coreGather_volume_le_six s width radius L hwidth hradius
  have hc : jobs.length*width ≤ 2*s :=
    (Nat.mul_le_mul_right width (List.length_filter_le _ _)).trans
      (coreSlots_le_two s width hwidth)
  have hn : jobs.length ≤ 2*s := by
    have hh := Nat.mul_le_mul_left jobs.length (show 1 ≤ width by omega)
    omega
  have hb : jobs.length*(2*L+1) ≤ 14*s := by
    dsimp only [jobs]
    dsimp only [jobs] at hn
    nlinarith only [hv,hn]
  exact hs.trans (by nlinarith only [Nat.mul_le_mul_right (cw*p+1) hb])

theorem computedFittingCyclicPassSchedule_fast_le (ct ce cw cV : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
      [NeZero (Sizes.s n i)] (width band depth L replicas : ℕ),
      0 < width → width ≤ Sizes.s n i → depth*band ≤ width → 1 ≤ band →
      Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width →
      (Sizes.p n)^2+band^2 ≤ width →
      ∀ H K : ℕ → ReplicaHaloProblem (Sizes.s n i),
      ∀ N w : ℕ → ℕ,
      (∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L,
        (H k).p = Sizes.p n ∧ (H k).t = Sizes.t n i ∧ (H k).band = band ∧
        (H k).origin = coreStart width k-depth*band ∧
        (H k).span = min L (Sizes.s n i-(coreStart width k-depth*band)) ∧
        (K k).p = Sizes.p n ∧ (K k).t = Sizes.t n i ∧ (K k).band = band ∧
        (K k).span = L-min L (Sizes.s n i-(coreStart width k-depth*band))) →
      (∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L,
        (H k).l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        (K k).l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        (H k).u ≤ Sizes.p n ∧ (K k).u ≤ Sizes.p n ∧
        (H k).target ≤ ct*Sizes.p n ∧ (K k).target ≤ ct*Sizes.p n ∧
        (H k).rhsExp ≤ ce*Sizes.p n ∧ (K k).rhsExp ≤ ce*Sizes.p n ∧
        (H k).Fs.length = replicas ∧ (K k).Fs.length = replicas ∧
        (H k).wordWidth = w k ∧ (K k).wordWidth = w k ∧
        w k ≤ cw*Sizes.p n ∧ (H k).metadataWidth ≤ cV*Sizes.p n ∧
        (K k).metadataWidth ≤ cV*Sizes.p n) →
      let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
      ((jobs.map (fun k => cachedReplicaPassCost (H k)+cachedReplicaPassCost (K k)+
        solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (w k))).sum : ℝ) ≤
      (jobs.map (fun k => initializedReplicaHaloSharedTime (H k)+cachedReplicaCouplingSharedTime (H k)+24+
        (initializedReplicaHaloSharedTime (K k)+cachedReplicaCouplingSharedTime (K k)+24)+
        solvedCyclicRecoverySharedTime (H k) (K k))).sum+
      300*replicas*((jobs.map (fun k => (N k+L+1)*(w k+1))).sum : ℝ)+
      680*E*replicas*((Sizes.s n i+(Sizes.t n i-Sizes.s n i)*band^2 : ℕ) : ℝ)*
        (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨F,hF,hfirst⟩ := selectedCachedReplicaPass_local_fast_le ct ce
  obtain ⟨D,hD,hrecovery⟩ := solvedCyclicRecovery_steps_local_fast_le cw cV
  refine ⟨F+D,add_nonneg hF hD,?_⟩
  intro n h i _ width band depth L replicas hw hwidth hguard hband hcell hprepare H K N w hgeom hparams
  dsimp only
  let jobs := coreGatherIndices (Sizes.s n i) width (depth*band) L
  let P : ℝ := (Sizes.p n : ℝ)^(129/128 : ℝ)
  have hs := sum_schedule_le jobs
    (fun k => cachedReplicaPassCost (H k)+cachedReplicaPassCost (K k)+
      solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (w k))
    (fun k => initializedReplicaHaloSharedTime (H k)+cachedReplicaCouplingSharedTime (H k)+24+
      (initializedReplicaHaloSharedTime (K k)+cachedReplicaCouplingSharedTime (K k)+24)+
      solvedCyclicRecoverySharedTime (H k) (K k))
    (fun k => (N k+L+1)*(w k+1))
    (fun k => replicaRecoveryLocalVolume (H k)+replicaRecoveryLocalVolume (K k))
    (300*replicas) ((F+D)*replicas*P) (by
      intro k hk
      obtain ⟨hpH,htH,hbH,haH,hsH,hpK,htK,hbK,hsK⟩ := hgeom k hk
      obtain ⟨hlH,hlK,huH,huK,htargetH,htargetK,hrhsH,hrhsK,hH,hK,hwH,hwK,hwidth,hVH,hVK⟩ := hparams k hk
      have hfirstH := hfirst h i (H k) hpH htH hlH huH htargetH hrhsH _ (le_refl _)
      have hfirstK := hfirst h i (K k) hpK htK hlK huK htargetK hrhsK _ (le_refl _)
      have hspan : (H k).span+(K k).span ≤ L := by rw [hsH,hsK]; omega
      have hr := hrecovery (H k) (K k) replicas (N k) L (w k) hH hK hwH hwK hspan
        (by simpa only [hwH,hpH] using hwidth) (by simpa only [hpH] using hVH)
        (by simpa only [hwK,hpK] using hwidth) (by simpa only [hpK] using hVK)
        _ (le_refl _)
      rw [hH,hpH] at hfirstH
      rw [hK,hpK] at hfirstK
      rw [hpH,hpK] at hr
      dsimp only [P]
      push_cast at hfirstH hfirstK hr ⊢
      nlinarith only [hfirstH,hfirstK,hr])
  have hv := (Nat.cast_le (α := ℝ)).mpr
    (computedFittingCyclicRecoveryLocalVolume_sum_le (h.good.lt i) (Sizes.p n)
      width band depth L hw hwidth hguard hband hcell hprepare H K hgeom)
  have hm := mul_le_mul_of_nonneg_left hv
    (by dsimp only [P]; positivity : (0 : ℝ) ≤ (F+D)*replicas*P)
  dsimp only [jobs,P] at hs hm
  push_cast at hs hm ⊢
  nlinarith only [hs,hm]

end IntegerMultBounds.MathlibTM2.Cost
