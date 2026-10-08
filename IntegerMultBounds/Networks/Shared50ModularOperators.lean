import IntegerMultBounds.Networks.Shared50GlobalShear
import IntegerMultBounds.Swap.Interchange

/-! Fixed finite coordinates and modular field programs for every actual signed
global edge operator. One prime works for all digit widths, with exactly the
proved global rank budget many recursive interchange operations. This does not
yet transport the complete routed network to modular addresses or tapes. -/

namespace IntegerMultBounds.Networks.Shared50ModularOperators

noncomputable section
open Shared50GlobalBudget (Ambient Triple)
open Shared50InvocationProjectionRank (rangeRank)

/-- Fix the finite coordinate basis once, using the proved ambient dimension. -/
def basis : Module.Basis (Fin 125000) ℚ Ambient :=
  Module.finBasisOfFinrankEq ℚ Ambient Shared50GlobalBudget.ambient_finrank

/-- Coordinate matrix of the actual rational address operator. -/
def matrix (op : Ambient →ₗ[ℚ] Ambient) : Matrix (Fin 125000) (Fin 125000) ℚ :=
  LinearMap.toMatrix basis basis op

@[simp] theorem matrix_sub (new old : Ambient →ₗ[ℚ] Ambient) :
    matrix (new - old) = matrix new - matrix old := map_sub (LinearMap.toMatrix basis basis) new old

@[simp] theorem matrix_neg (op : Ambient →ₗ[ℚ] Ambient) : matrix (-op) = -matrix op :=
  map_neg (LinearMap.toMatrix basis basis) op

@[simp] theorem matrix_id : matrix (LinearMap.id : Ambient →ₗ[ℚ] Ambient) = 1 :=
  LinearMap.toMatrix_id basis

/-- Coordinate conversion preserves the genuine range dimension. -/
theorem matrix_rank (op : Ambient →ₗ[ℚ] Ambient) : (matrix op).rank = rangeRank op := by
  rw [matrix,Matrix.rank_eq_finrank_range_toLin _ basis basis,Matrix.toLin_toMatrix]
  rfl

/-- Ordered coordinate matrices, including every signed first-boundary edge. -/
def matrices {n : ℕ} (e : Fin n ≃ Triple) : List (Matrix (Fin 125000) (Fin 125000) ℚ) :=
  (Shared50GlobalShear.operators e).map matrix

theorem matrices_rankSum {n : ℕ} (e : Fin n ≃ Triple) :
    ((matrices e).map Matrix.rank).sum = Shared50GlobalShear.rankSum e := by
  simp only [matrices,List.map_map,Function.comp_def,matrix_rank]
  rfl

/-- The concrete signed operator family has exactly the optimized rank sum. -/
theorem matrices50_rankSum :
    ((matrices Shared50GlobalCircuit.enumeration).map Matrix.rank).sum = Shared50Parameters.s := by
  rw [matrices_rankSum,Shared50GlobalShear.rankSum50_exact]

section Schedules
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Reuse the existing ordered modular-shear theorem for an arbitrary operator
list, preserving its repetitions and its rational rank counts. -/
theorem exists_prime_programs (As : List (Matrix ι ι ℚ)) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ b : ℕ,
      ∃ ps : List (List (Swap.Shear.Op ι (ZMod (q ^ b)))),
        List.Forall₂ (fun A p => Swap.Shear.interchanges p = A.rank ∧
          ∀ state, Swap.Shear.run p state =
            ShearFrame.address (Matrix.toLin' (Swap.Modular.reduce (q ^ b) A)) state) As ps ∧
        (ps.map Swap.Shear.interchanges).sum = (As.map Matrix.rank).sum := by
  obtain ⟨q,hq,hodd,h⟩ := Swap.Interchange.exists_prime_schedule (As.map fun A => (0,A))
  refine ⟨q,hq,hodd,?_⟩
  intro b
  obtain ⟨ps,hps,hcount⟩ := h b
  refine ⟨ps,?_,?_⟩
  · simpa only [List.forall₂_map_left_iff,sub_zero] using hps
  · simpa only [List.map_map,Function.comp_def,sub_zero] using hcount
end Schedules

/-- A single fixed odd prime implements every actual edge matrix at every
radix exponent, with exactly the certified total number of interchanges. -/
theorem exists_prime_actual :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ b : ℕ,
      ∃ ps : List (List (Swap.Shear.Op (Fin 125000) (ZMod (q ^ b)))),
        List.Forall₂ (fun A p => Swap.Shear.interchanges p = A.rank ∧
          ∀ state, Swap.Shear.run p state =
            ShearFrame.address (Matrix.toLin' (Swap.Modular.reduce (q ^ b) A)) state)
          (matrices Shared50GlobalCircuit.enumeration) ps ∧
        (ps.map Swap.Shear.interchanges).sum = Shared50Parameters.s := by
  obtain ⟨q,hq,hodd,h⟩ := exists_prime_programs (matrices Shared50GlobalCircuit.enumeration)
  refine ⟨q,hq,hodd,?_⟩
  intro b
  obtain ⟨ps,hps,hcount⟩ := h b
  exact ⟨ps,hps,hcount.trans matrices50_rankSum⟩

/-- Equivalent statement indexed by the actual rational operators themselves. -/
theorem exists_prime_actual_operators :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ b : ℕ,
      ∃ ps : List (List (Swap.Shear.Op (Fin 125000) (ZMod (q ^ b)))),
        List.Forall₂ (fun op p => Swap.Shear.interchanges p = rangeRank op ∧
          ∀ state, Swap.Shear.run p state =
            ShearFrame.address (Matrix.toLin' (Swap.Modular.reduce (q ^ b) (matrix op))) state)
          (Shared50GlobalShear.operators Shared50GlobalCircuit.enumeration) ps ∧
        (ps.map Swap.Shear.interchanges).sum = Shared50Parameters.s := by
  obtain ⟨q,hq,hodd,h⟩ := exists_prime_actual
  refine ⟨q,hq,hodd,?_⟩
  intro b
  obtain ⟨ps,hps,hcount⟩ := h b
  refine ⟨ps,?_,hcount⟩
  simpa only [matrices,List.forall₂_map_left_iff,matrix_rank] using hps

end
end IntegerMultBounds.Networks.Shared50ModularOperators
