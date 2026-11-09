module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicRecoverySchedule
import Mathlib.Tactic.Linarith

/-! Absorb every shared first-pass, mask and recovery charge of the cyclic
caller at its actual schedule frequency, independently of replica count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem shared_schedule_le {ι : Type} {s : ℕ} [NeZero s]
    (jobs : List ι) (H K : ι → ReplicaHaloProblem s) :
    (jobs.map (fun j => initializedReplicaHaloSharedTime (H j)+cachedReplicaCouplingSharedTime (H j)+24+
      (initializedReplicaHaloSharedTime (K j)+cachedReplicaCouplingSharedTime (K j)+24)+
      solvedCyclicRecoverySharedTime (H j) (K j)+
      (placedReplicaBoundaryMaskCost (H j)+placedReplicaBoundaryMaskCost (K j)))).sum ≤
    (jobs.map (fun j => initializedReplicaHaloSharedTime (H j))).sum+
    (jobs.map (fun j => initializedReplicaHaloSharedTime (K j))).sum+
    (jobs.map (fun j => cachedReplicaCouplingSharedTime (H j))).sum+
    (jobs.map (fun j => cachedReplicaCouplingSharedTime (K j))).sum+
    4*(jobs.map (fun j => solvedCyclicRecoverySharedTime (H j) (K j))).sum := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hj : 48+solvedCyclicRecoverySharedTime (H j) (K j)+
        (placedReplicaBoundaryMaskCost (H j)+placedReplicaBoundaryMaskCost (K j)) ≤
        4*solvedCyclicRecoverySharedTime (H j) (K j) := by
      unfold solvedCyclicRecoverySharedTime
      omega
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hj,ih]

theorem selectedCyclicCallerSharedSchedule_volume_le (cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ (jobs : List ι)
      (H K : ι → ReplicaHaloProblem (Sizes.s n i)),
      jobs.length ≤ 2*Sizes.t n i →
      (∀ j ∈ jobs, ∀ R ∈ [H j,K j],
        R.p = Sizes.p n ∧ R.t = Sizes.t n i ∧ R.u ≤ R.p ∧ R.l ≤ cl*R.p ∧
        R.wordWidth ≤ cw*R.p ∧ 2^R.l ≤ cr*R.p ∧ R.metadataWidth ≤ cV*R.p) →
      scale*(jobs.map (fun j => initializedReplicaHaloSharedTime (H j)+cachedReplicaCouplingSharedTime (H j)+24+
        (initializedReplicaHaloSharedTime (K j)+cachedReplicaCouplingSharedTime (K j)+24)+
        solvedCyclicRecoverySharedTime (H j) (K j)+
        (placedReplicaBoundaryMaskCost (H j)+placedReplicaBoundaryMaskCost (K j)))).sum ≤ Sizes.T n := by
  filter_upwards [selectedReplicaHaloSharedSchedule_volume_le cl cw cr cV (8*scale),
    selectedCachedCouplingSharedSchedule_volume_le cw cV (8*scale),
    selectedCyclicRecoverySharedSchedule_volume_le cV (8*scale)] with n hhalo hcoupling hrecovery
  intro ι h i _ jobs H K hcount hparams
  have hH := fun j hj => hparams j hj (H j) (by simp)
  have hK := fun j hj => hparams j hj (K j) (by simp)
  have hhH := hhalo i jobs H hcount hH
  have hhK := hhalo i jobs K hcount hK
  have hcH := hcoupling h i jobs H hcount (by
    intro j hj
    obtain ⟨hp,ht,hu,hl,hw,hr,hV⟩ := hH j hj
    exact ⟨hp,ht,hw,hu,hV⟩)
  have hcK := hcoupling h i jobs K hcount (by
    intro j hj
    obtain ⟨hp,ht,hu,hl,hw,hr,hV⟩ := hK j hj
    exact ⟨hp,ht,hw,hu,hV⟩)
  have hr := hrecovery h i jobs H K hcount (by
    intro j hj
    obtain ⟨hpH,_,_,_,_,_,hVH⟩ := hH j hj
    obtain ⟨hpK,_,_,_,_,_,hVK⟩ := hK j hj
    exact ⟨by simpa only [hpH] using hVH,by simpa only [hpK] using hVK⟩)
  have hs := Nat.mul_le_mul_left (8*scale) (shared_schedule_le jobs H K)
  nlinarith only [hhH,hhK,hcH,hcK,hr,hs]

end IntegerMultBounds.MathlibTM2.Cost
