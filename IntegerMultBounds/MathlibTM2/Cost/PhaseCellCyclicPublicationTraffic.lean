module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPackedPublicationMerge
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveControls
public import IntegerMultBounds.NLogN.PhaseCellCoreGatherVolume
public import IntegerMultBounds.NLogN.PhaseCellCoreLocalityGeometry
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! The remaining executed complex-core merge, crop and component-assembly
traffic is linear in the encoded halo volume, including fixed controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellMatrix

def cyclicPublicationTrafficCost (leftSpan rightSpan w W radius core n replicas fields : ℕ) : ℕ :=
  ((replicas*(retainedPackedPublicationMergeCost leftSpan w+5)+4)+
    (replicas*(retainedPackedPublicationMergeCost rightSpan w+5)+4))+
  (packedCoreArchiveControlsCost radius core W replicas+
    (replicas*(packedCoreArchiveStepCost radius core n W+3)+2)+
    (2*(radius*W+core*W+n)+7))+
  ((6*fields+4)+((core*(4*W+9)+4)+
    (fields*(16*(core*W)+9)+14)+(2*(core*W)+2))+(2*fields+2))

theorem cyclicPublicationTrafficCost_le_volume
    (leftSpan rightSpan w W radius core n replicas fields : ℕ)
    (hspan : leftSpan+rightSpan ≤ n) (hhalo : core+2*radius ≤ n) (hfields : fields ≤ replicas) :
    cyclicPublicationTrafficCost leftSpan rightSpan w W radius core n replicas fields ≤
      1000*(replicas+1)*(n+1)*(w+W+1) := by
  have hl : leftSpan ≤ n := by omega
  have hr : rightSpan ≤ n := by omega
  have hcore : core ≤ n := by omega
  have hrad : radius ≤ n := by omega
  calc
    _ ≤ cyclicPublicationTrafficCost n n w W n n n replicas replicas := by
      unfold cyclicPublicationTrafficCost retainedPackedPublicationMergeCost
        packedCoreArchiveControlsCost packedCoreArchiveStepCost retireCountedLineCost
      gcongr
    _ ≤ _ := by
      unfold cyclicPublicationTrafficCost retainedPackedPublicationMergeCost
        packedCoreArchiveControlsCost packedCoreArchiveStepCost retireCountedLineCost
      ring_nf
      omega

private theorem sum_uniform_le {ι : Type} (jobs : List ι) (cost : ι → ℕ) (B : ℕ)
    (h : ∀ k ∈ jobs, cost k ≤ B) : (jobs.map cost).sum ≤ jobs.length*B := by
  induction jobs with
  | nil => simp
  | cons k jobs ih =>
    have hk := h k (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Merge, crop and component assembly on one computed fitting class retain
only linear encoded axis traffic, including the actual fixed controls. -/
theorem computedFittingCyclicPublicationTraffic_sum_le
    (s width radius L p cw W replicas : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hradius : radius ≤ width) (leftSpan rightSpan w fields : ℕ → ℕ)
    (hparams : ∀ k ∈ coreGatherIndices s width radius L,
      leftSpan k+rightSpan k ≤ L ∧ w k ≤ cw*p ∧ fields k ≤ replicas) :
    ((coreGatherIndices s width radius L).map (fun k =>
      cyclicPublicationTrafficCost (leftSpan k) (rightSpan k) (w k) W radius
        (coreLength s width k) L replicas (fields k))).sum ≤
      7000*(replicas+1)*s*(cw*p+W+1) := by
  let jobs := coreGatherIndices s width radius L
  have hs := sum_uniform_le jobs (fun k =>
    cyclicPublicationTrafficCost (leftSpan k) (rightSpan k) (w k) W radius
      (coreLength s width k) L replicas (fields k))
    (1000*(replicas+1)*(L+1)*(cw*p+W+1)) (by
      intro k hk
      obtain ⟨hspan,hw,hfields⟩ := hparams k hk
      have hlen := (coreGatherIndices_spec s width radius L k hk).2.2
      have hc := cyclicPublicationTrafficCost_le_volume (leftSpan k) (rightSpan k) (w k) W
        radius (coreLength s width k) L replicas (fields k) hspan (by omega) hfields
      have hm := Nat.mul_le_mul_left (1000*(replicas+1)*(L+1))
        (show w k+W+1 ≤ cw*p+W+1 by omega)
      exact hc.trans hm)
  have hv := coreGather_volume_le_six s width radius L hwidth hradius
  have hc := coreGatherIndices_length_le s width radius L hw
  have hlen : jobs.length*(L+1) ≤ 7*s := by
    dsimp only [jobs]
    nlinarith only [hv,hc]
  have hm := Nat.mul_le_mul_right (1000*(replicas+1)*(cw*p+W+1)) hlen
  apply hs.trans
  nlinarith only [hm]

end IntegerMultBounds.MathlibTM2.Cost
