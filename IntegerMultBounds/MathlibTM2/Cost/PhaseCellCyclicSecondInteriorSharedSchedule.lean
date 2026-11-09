module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoverySharedSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaProblemLayout
import Mathlib.Tactic.Linarith

/-! Shared second-interior setup inherits selected bounds through SameLayout. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem shared_second_sum_le {ι : Type} {s : ℕ} [NeZero s]
    (jobs : List ι) (J M : ι → ReplicaHaloProblem s) :
    (jobs.map (fun j => initializedReplicaHaloSharedTime (J j)+
      initializedReplicaHaloSharedTime (M j)+36)).sum ≤
    5*(jobs.map (fun j => initializedReplicaHaloSharedTime (J j))).sum+
      (jobs.map (fun j => initializedReplicaHaloSharedTime (M j))).sum := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hc : 36 ≤ 4*initializedReplicaHaloSharedTime (J j) := by
      unfold initializedReplicaHaloSharedTime
      omega
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hc,ih]

theorem selectedCyclicSecondInteriorSharedSchedule_volume_le (cl cw cr cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι : Type} (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (jobs : List ι) (H K J M : ι → ReplicaHaloProblem (Sizes.s n i)),
      jobs.length ≤ 2*Sizes.t n i →
      (∀ j ∈ jobs, (H j).SameLayout (J j) ∧ (K j).SameLayout (M j)) →
      (∀ j ∈ jobs, ∀ R ∈ [H j,K j], R.p = Sizes.p n ∧ R.t = Sizes.t n i ∧
        R.u ≤ R.p ∧ R.l ≤ cl*R.p ∧ R.wordWidth ≤ cw*R.p ∧
        2^R.l ≤ cr*R.p ∧ R.metadataWidth ≤ cV*R.p) →
      scale*(jobs.map (fun j => initializedReplicaHaloSharedTime (J j)+
        initializedReplicaHaloSharedTime (M j)+36)).sum ≤ Sizes.T n := by
  filter_upwards [selectedReplicaHaloSharedSchedule_volume_le cl cw cr cV (6*scale)] with n hs
  intro ι i _ jobs H K J M hcount hlayout hparams
  have hJ := hs i jobs J hcount (by
    intro j hj
    have layout := (hlayout j hj).1
    simpa only [layout.p,layout.t,layout.u,layout.l,layout.wordWidth,layout.metadataWidth]
      using hparams j hj (H j) (by simp))
  have hM := hs i jobs M hcount (by
    intro j hj
    have layout := (hlayout j hj).2
    simpa only [layout.p,layout.t,layout.u,layout.l,layout.wordWidth,layout.metadataWidth]
      using hparams j hj (K j) (by simp))
  have hb := Nat.mul_le_mul_left (6*scale) (shared_second_sum_le jobs J M)
  nlinarith only [hJ,hM,hb]

end IntegerMultBounds.MathlibTM2.Cost
