module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicPassScheduleFast
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCyclicBoundaryLedger
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
import Mathlib.Tactic.Linarith

/-! The actual fitting caller ledger, summed before applying numerical estimates.
Only controller traffic is absorbed here; every setup keeps its multiplicity. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_components_le {ι : Type} (jobs : List ι)
    (cost pass factory mask batch traffic : ι → ℕ) (A : ℕ)
    (h : ∀ j ∈ jobs, cost j ≤ pass j+factory j+mask j+batch j+A*traffic j) :
    (jobs.map cost).sum ≤ (jobs.map pass).sum+(jobs.map factory).sum+
      (jobs.map mask).sum+(jobs.map batch).sum+A*(jobs.map traffic).sum := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hj := h j (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons]
    nlinarith only [hj,hs]

theorem computedFittingCyclicCaller_schedule_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p u l width depth L target replicas cw : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hguard : depth*PhaseCellBand.width p u ≤ width)
    (H K : ℕ → ReplicaHaloProblem s) (q : ℕ → ℕ)
    (hparams : ∀ k ∈ coreGatherIndices s width (depth*PhaseCellBand.width p u) L,
      (H k).Fs.length = replicas ∧ (K k).Fs.length = replicas ∧
      (H k).wordWidth = 2*q k+8 ∧ (K k).wordWidth = 2*q k+8 ∧
      (H k).span+(K k).span ≤ L ∧ 2*q k+8 ≤ cw*p) :
    let jobs := coreGatherIndices s width (depth*PhaseCellBand.width p u) L
    let N := fun k => (cyclicPrincipalBoundary s t (PhaseCellBand.width p u)
      (coreStart width k-depth*PhaseCellBand.width p u) L).card
    ((jobs.map (fun k => cachedCyclicReplicaBoundaryBill (H k) (K k) p u l t
      (coreStart width k-depth*PhaseCellBand.width p u) L target (q k) (2*q k+8)
      (N k) (24*PhaseCellBand.width p u+1) replicas+
      solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (2*q k+8))).sum) ≤
    (jobs.map (fun k => cachedReplicaPassCost (H k)+cachedReplicaPassCost (K k)+
      solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (2*q k+8))).sum+
    (jobs.map (fun k => constructedCyclicFactorCost p u l s t
      (coreStart width k-depth*PhaseCellBand.width p u) L target 2)).sum+
    (jobs.map (fun k => placedReplicaBoundaryMaskCost (H k)+placedReplicaBoundaryMaskCost (K k))).sum+
    (jobs.map (fun k => preparedResidualBatchCost (q k) (2*q k+8)
      (N k) (24*PhaseCellBand.width p u+1) replicas)).sum+
    2800*(replicas+1)*s*(cw*p+1) := by
  dsimp only
  let jobs := coreGatherIndices s width (depth*PhaseCellBand.width p u) L
  let N := fun k => (cyclicPrincipalBoundary s t (PhaseCellBand.width p u)
    (coreStart width k-depth*PhaseCellBand.width p u) L).card
  have htraffic := computedFittingCyclicTraffic_sum_le s width
    (depth*PhaseCellBand.width p u) L p cw hw hwidth hguard N (fun k => 2*q k+8) (by
      intro k hk
      obtain ⟨hl,hr,hL⟩ := coreGatherIndices_spec s width (depth*PhaseCellBand.width p u) L k hk
      have hstart := coreIndex_start_lt s width k hw (List.mem_filter.mp hk).1
      have ha : coreStart width k-depth*PhaseCellBand.width p u < s := by omega
      have hn : L ≤ s := by omega
      exact ⟨(cyclicPrincipalBoundary_card t _ _ L hst ha hn).trans (Nat.min_le_left _ _),
        (hparams k hk).2.2.2.2.2⟩)
  have hs := sum_components_le jobs
    (fun k => cachedCyclicReplicaBoundaryBill (H k) (K k) p u l t
      (coreStart width k-depth*PhaseCellBand.width p u) L target (q k) (2*q k+8)
      (N k) (24*PhaseCellBand.width p u+1) replicas+
      solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (2*q k+8))
    (fun k => cachedReplicaPassCost (H k)+cachedReplicaPassCost (K k)+
      solvedCyclicRecoveryCost (H k) (K k) replicas (N k) L (2*q k+8))
    (fun k => constructedCyclicFactorCost p u l s t
      (coreStart width k-depth*PhaseCellBand.width p u) L target 2)
    (fun k => placedReplicaBoundaryMaskCost (H k)+placedReplicaBoundaryMaskCost (K k))
    (fun k => preparedResidualBatchCost (q k) (2*q k+8) (N k)
      (24*PhaseCellBand.width p u+1) replicas)
    (fun k => (N k+L+1)*(2*q k+8+1)) (200*(replicas+1)) (by
      intro k hk
      obtain ⟨hH,hK,hwH,hwK,hspan,_⟩ := hparams k hk
      have hc := cachedCyclicReplicaBoundaryBill_le_components (H k) (K k) p u l t
        (coreStart width k-depth*PhaseCellBand.width p u) L target (q k) (2*q k+8)
        (N k) (24*PhaseCellBand.width p u+1) replicas hH hK hwH hwK hspan
      nlinarith only [hc])
  dsimp only [jobs,N] at hs htraffic
  nlinarith only [hs,Nat.mul_le_mul_left (200*(replicas+1)) htraffic]

end IntegerMultBounds.MathlibTM2.Cost
