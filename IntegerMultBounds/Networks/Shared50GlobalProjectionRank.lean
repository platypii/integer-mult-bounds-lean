import IntegerMultBounds.Networks.Shared50GlobalTraceStages
import IntegerMultBounds.Networks.Shared50InvocationProjectionRank

/-! Actual projector-difference ranks of the optimized reused two-bank trace.
Every local and global loss, nesting, and nondegeneracy premise is discharged.
The corrected budget includes one source-dimension contribution; its realization
as the signed first boundary is supplied by Shared50SignedBoundary. -/

namespace IntegerMultBounds.Networks.Shared50GlobalProjectionRank

noncomputable section
open Shared50GlobalTrace Shared50GlobalTraceStages
open Shared50GlobalBudget (Triple Ambient sourceTotal sinkTotal)
open Shared50ReuseLabels (cubeForm cube_symm)
open Shared50InvocationProjectionRank (rangeRank)

variable {n : ℕ}

/-- Genuine projector-difference matrices in the actual global trace order. -/
def operators (e : Fin n ≃ Triple) : List (Ambient →ₗ[ℚ] Ambient) :=
  Shared50InvocationProjectionRank.operators cubeForm cube_symm source (trace e)

/-- Sum of range dimensions of the actual global projector differences. -/
def rankSum (e : Fin n ≃ Triple) : ℕ := ((operators e).map rangeRank).sum

theorem rank_balance (e : Fin n ≃ Triple) :
    rankSum e + sourceTotal = sinkTotal + 2 * (3 * n ^ 2 * 2500) := by
  have hb := Shared50InvocationProjectionRank.operator_balance cubeForm cube_symm
    source (trace e) (trace_nondegenerate e) (trace_comparable e)
  rw [trace_finish,trace_loss] at hb
  exact hb

/-- The fixed certified enumeration gives the selected 19,600 inputs. -/
def rankSum50 : ℕ := rankSum Shared50GlobalCircuit.enumeration

theorem rank_balance50 : rankSum50 + sourceTotal = sinkTotal + 2 * Shared50Parameters.L := by
  have hb := rank_balance Shared50GlobalCircuit.enumeration
  have hl : 3 * 19600 ^ 2 * 2500 = Shared50Parameters.L := by
    rw [Shared50Parameters.loss_count]
    norm_num
  rw [hl] at hb
  exact hb

/-- No supplied rank-balance or loss bound: both come from the actual trace. -/
theorem corrected_rank_budget : rankSum50 + sourceTotal ≤ Shared50Parameters.s :=
  Shared50GlobalBudget.corrected_rank_budget _ _ rank_balance50 le_rfl

theorem corrected_rank_exact : rankSum50 + sourceTotal = Shared50Parameters.s := by
  have hb := Shared50GlobalBudget.balance_dimensions _ _ rank_balance50
  have hs := Shared50Parameters.rank_balance
  rw [Shared50GlobalBudget.source_total_eq_N]
  omega

/-- Strict optimized branching inequality for the complete actual trace budget. -/
theorem branching_bound :
    ((rankSum50 + sourceTotal : ℕ) : ℝ) / Shared50Parameters.W <
      (Shared50Parameters.m : ℝ) ^ Parameters.tau :=
  Shared50GlobalBudget.branching_of_balance _ _ rank_balance50 le_rfl

end
end IntegerMultBounds.Networks.Shared50GlobalProjectionRank
