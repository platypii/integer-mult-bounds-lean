module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedCyclicRecovery
import Mathlib.Tactic.Ring

/-! Separate the actual recovery bill by execution frequency. In particular,
the row reversals inside preparation are replica work, not shared setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Host
variable {s : ℕ}

/-- Masks and constant loop overhead, independent of the number of RHS rows. -/
def solvedCyclicRecoverySharedTime (H K : ReplicaHaloProblem s) : ℕ :=
  placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K+
    initializeRecoveryMasksCost H.metadataWidth H.span H.band+
    initializeRecoveryMasksCost K.metadataWidth K.span K.band+24

/-- One native projection, two retained couplings, and both archive reversals. -/
def solvedCyclicRecoveryReplicaTime (H K : ReplicaHaloProblem s) (N n w : ℕ) : ℕ :=
  nativeCyclicBoundaryRowCost N n w+
    cyclicRecoveryCouplingPieceCost H+cyclicRecoveryCouplingPieceCost K+
    16*(H.span*H.wordWidth)+16*(K.span*K.wordWidth)+52

/-- The two pieces partition one window: reversal and archive traffic is
linear in that window's volume, while the numerical couplings stay explicit. -/
theorem solvedCyclicRecoveryReplicaTime_le_window
    (H K : ReplicaHaloProblem s) (N n w : ℕ)
    (hH : H.wordWidth = w) (hK : K.wordWidth = w)
    (hspan : H.span+K.span ≤ n) :
    solvedCyclicRecoveryReplicaTime H K N n w ≤
      nativeCyclicBoundaryRowCost N n w+cachedRecoveryCouplingRowCost H+
        cachedRecoveryCouplingRowCost K+28*(n*w)+76 := by
  have hv := Nat.mul_le_mul_right w hspan
  unfold solvedCyclicRecoveryReplicaTime cyclicRecoveryCouplingPieceCost
  rw [hH,hK]
  ring_nf at hv ⊢
  omega

theorem solvedCyclicRecoveryCost_eq_shared_add_replicas
    (H K : ReplicaHaloProblem s) (replicas N n w : ℕ)
    (hH : H.Fs.length = replicas) (hK : K.Fs.length = replicas) :
    solvedCyclicRecoveryCost H K replicas N n w =
      solvedCyclicRecoverySharedTime H K+
        replicas*solvedCyclicRecoveryReplicaTime H K N n w := by
  unfold solvedCyclicRecoveryCost solvedCyclicRecoverySharedTime
    solvedCyclicRecoveryReplicaTime nativeCyclicBoundaryBatchCost
    preparedProjectedCyclicRecoveryCost replicaRecoveryPreparationCost reverseCopyRowsCost
  rw [hH,hK]
  ring

private theorem sum_map_split {ι : Type*} (jobs : List ι) (cost shared repeated : ι → ℕ)
    (h : ∀ j ∈ jobs, cost j = shared j+repeated j) :
    (jobs.map cost).sum = (jobs.map shared).sum+(jobs.map repeated).sum := by
  calc
    _ = (jobs.map (fun j => shared j+repeated j)).sum :=
      congrArg List.sum (List.map_congr_left h)
    _ = _ := List.sum_map_add

/-- The cyclic split supplies its own volume conservation, including a window
that wraps at the physical period cut. Setup is still charged only once. -/
theorem solvedCyclicRecoveryCost_le_partition
    (H K : ReplicaHaloProblem s) (replicas N n w a : ℕ)
    (hH : H.Fs.length = replicas) (hK : K.Fs.length = replicas)
    (hHW : H.wordWidth = w) (hKW : K.wordWidth = w)
    (hHN : H.span = min n (s-a)) (hKN : K.span = n-min n (s-a)) :
    solvedCyclicRecoveryCost H K replicas N n w ≤
      solvedCyclicRecoverySharedTime H K+
        replicas*(nativeCyclicBoundaryRowCost N n w+cachedRecoveryCouplingRowCost H+
          cachedRecoveryCouplingRowCost K+28*(n*w)+76) := by
  rw [solvedCyclicRecoveryCost_eq_shared_add_replicas H K replicas N n w hH hK]
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  apply solvedCyclicRecoveryReplicaTime_le_window H K N n w hHW hKW
  rw [hHN,hKN]
  omega

/-- Sum the executed bills without multiplying shared preparation by replicas.
The schedule may repeat cores; its actual multiplicity is preserved here. -/
theorem solvedCyclicRecoveryCost_sum {ι : Type*} (jobs : List ι)
    (H K : ι → ReplicaHaloProblem s) (replicas N n w : ι → ℕ)
    (hH : ∀ j ∈ jobs, (H j).Fs.length = replicas j)
    (hK : ∀ j ∈ jobs, (K j).Fs.length = replicas j) :
    (jobs.map (fun j => solvedCyclicRecoveryCost (H j) (K j)
      (replicas j) (N j) (n j) (w j))).sum =
    (jobs.map (fun j => solvedCyclicRecoverySharedTime (H j) (K j))).sum+
      (jobs.map (fun j => replicas j*solvedCyclicRecoveryReplicaTime
        (H j) (K j) (N j) (n j) (w j))).sum := by
  apply sum_map_split
  intro j hj
  exact solvedCyclicRecoveryCost_eq_shared_add_replicas _ _ _ _ _ _ (hH j hj) (hK j hj)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
