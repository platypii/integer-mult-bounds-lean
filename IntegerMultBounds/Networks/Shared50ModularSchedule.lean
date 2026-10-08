import IntegerMultBounds.Networks.Shared50ModularOperators
import IntegerMultBounds.Networks.Shared50OperatorPairs
import IntegerMultBounds.Networks.ModularFrameSchedule

/-! One simultaneous good prime for the actual signed physical matrix-pair
schedule and every routed source/sink endpoint. All ordered edge programs keep
the certified total rank, and their reduced endpoint contract is the identity.
This is the modular field schedule, not its execution by a tape machine. -/

namespace IntegerMultBounds.Networks.Shared50ModularSchedule

noncomputable section
open Shared50GlobalBudget (Triple World)
open Shared50GlobalTrace
open Shared50ShearEndpoints (projector route)
open Shared50ModularOperators (matrix matrix_rank matrix_sub matrix_neg matrix_id)
open Swap.Modular (Admissible reduce)
open ModularFrameSchedule (EdgeSpec)

abbrev Index := Fin 125000
abbrev Mat := Matrix Index Index ℚ

/-- Exact old/new coordinate matrices behind the ordered physical frame edges. -/
def pairs {n : ℕ} (e : Fin n ≃ Triple) : List (Mat × Mat) :=
  (Shared50OperatorPairs.pairs e).map (fun p => (matrix p.1,matrix p.2))

/-- The differences are precisely the matrices of the counted actual operators. -/
theorem differences {n : ℕ} (e : Fin n ≃ Triple) :
    (pairs e).map (fun p => p.2 - p.1) = Shared50ModularOperators.matrices e := by
  rw [pairs,Shared50ModularOperators.matrices,← Shared50OperatorPairs.differences]
  simp only [List.map_map,Function.comp_def,matrix_sub]

theorem rankSum {n : ℕ} (e : Fin n ≃ Triple) :
    ((pairs e).map (fun p => (p.2 - p.1).rank)).sum = Shared50GlobalShear.rankSum e := by
  have hh := congrArg (fun As : List Mat => (As.map Matrix.rank).sum) (differences e)
  simpa only [List.map_map,Function.comp_def,Shared50ModularOperators.matrices_rankSum] using hh

theorem rankSum50 :
    ((pairs Shared50GlobalCircuit.enumeration).map (fun p => (p.2 - p.1).rank)).sum = Shared50Parameters.s := by
  rw [rankSum,Shared50GlobalShear.rankSum50_exact]

/-- The signed source coefficient matrix at an actual physical world role. -/
def sourceMatrix (i : World) : Mat := -matrix (projector (source i))

/-- The positive sink coefficient matrix at an actual physical world role. -/
def sinkMatrix (i : World) : Mat := matrix (projector (sink i))

/-- Every physical endpoint is protected by the same prime as every edge. -/
def extra : Finset Mat :=
  (wires.map sourceMatrix ++ wires.map sinkMatrix).toFinset

theorem sourceMatrix_mem (i : World) : sourceMatrix i ∈ extra := by
  rw [extra,List.mem_toFinset]
  exact List.mem_append_left _ (List.mem_map.mpr ⟨i,mem_wires i,rfl⟩)

theorem sinkMatrix_mem (i : World) : sinkMatrix i ∈ extra := by
  rw [extra,List.mem_toFinset]
  exact List.mem_append_right _ (List.mem_map.mpr ⟨i,mem_wires i,rfl⟩)

/-- The routed rational endpoint identity in the fixed finite coordinates. -/
theorem endpoint_matrix (i : World) : sinkMatrix i - sourceMatrix (route i) = 1 := by
  have hh := congrArg matrix (Shared50ShearEndpoints.routed_operator i)
  simpa only [matrix_sub,matrix_neg,matrix_id,sinkMatrix,sourceMatrix] using hh

/-- Reduction respects the complete routed endpoint identity once both actual
endpoint matrices have invertible denominators. -/
theorem reduced_endpoint (m : ℕ)
    (hsource : ∀ i, Admissible m (sourceMatrix i))
    (hsink : ∀ i, Admissible m (sinkMatrix i)) (i : World) :
    reduce m (sinkMatrix i) - reduce m (sourceMatrix (route i)) = 1 := by
  rw [← ModularFrameSchedule.reduce_sub m (hsink i) (hsource (route i)),endpoint_matrix,
    ModularFrameSchedule.reduce_id]

/-- The common prime is chosen before the radix exponent. Every physical edge
keeps its actual two endpoint matrices, and all routed endpoint reductions and
ordered field programs share that prime. -/
theorem exists_prime_actual :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧
      (∀ d ∈ ModularFrameSchedule.allDenominators (pairs Shared50GlobalCircuit.enumeration) extra, d < q) ∧
      ∀ b : ℕ,
        (∀ i, Admissible (q ^ b) (sourceMatrix i)) ∧
        (∀ i, Admissible (q ^ b) (sinkMatrix i)) ∧
        (∀ i, reduce (q ^ b) (sinkMatrix i) - reduce (q ^ b) (sourceMatrix (route i)) = 1) ∧
        ∃ ps : List (List (Swap.Shear.Op Index (ZMod (q ^ b)))),
          List.Forall₂ (EdgeSpec (q ^ b)) (pairs Shared50GlobalCircuit.enumeration) ps ∧
          (ps.map Swap.Shear.interchanges).sum = Shared50Parameters.s := by
  obtain ⟨q,hq,hodd,hd,h⟩ := ModularFrameSchedule.exists_prime_schedule_extra
    (pairs Shared50GlobalCircuit.enumeration) extra
  refine ⟨q,hq,hodd,hd,?_⟩
  intro b
  obtain ⟨he,ps,hps,hcount⟩ := h b
  have hsource : ∀ i, Admissible (q ^ b) (sourceMatrix i) := fun i => he _ (sourceMatrix_mem i)
  have hsink : ∀ i, Admissible (q ^ b) (sinkMatrix i) := fun i => he _ (sinkMatrix_mem i)
  exact ⟨hsource,hsink,reduced_endpoint (q ^ b) hsource hsink,ps,hps,hcount.trans rankSum50⟩

end
end IntegerMultBounds.Networks.Shared50ModularSchedule
