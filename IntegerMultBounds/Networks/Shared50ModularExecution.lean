import IntegerMultBounds.Networks.Shared50ModularSchedule
import IntegerMultBounds.Networks.Shared50SignedFramed
import IntegerMultBounds.Networks.Shared50ModularControl

/-! The actual signed physical network over finite prime-power addresses.
Every physical frame edge is implemented by its ordered modular address
program. Arbitrary stored arrays undergo the routed full shear, with the exact
certified interchange count. Tape layout and tape running time are separate. -/

namespace IntegerMultBounds.Networks.Shared50ModularExecution

noncomputable section
open Shared50GlobalBudget (World Triple)
open Shared50GlobalTrace
open Shared50ShearEndpoints (projector route)
open Shared50ModularOperators (matrix)
open Shared50ModularSchedule (Index Mat sourceMatrix sinkMatrix)
open Swap.Modular (Admissible reduce)
open FramedCircuit (Frame)

abbrev Vector (m : ℕ) := Index → ZMod m
abbrev Address (m : ℕ) := Vector m × Vector m
abbrev Arrays (m : ℕ) := Address m → ZMod 2

/-- Reduce a rational coefficient matrix, then use its finite address shear. -/
def matrixFrame (m : ℕ) (A : Mat) : Frame (ZMod 2) (Arrays m) :=
  ShearFrame.frame (Matrix.toLin' (reduce m A))

def frames (m : ℕ) (U : Label) : Frame (ZMod 2) (Arrays m) :=
  matrixFrame m (matrix (projector U))

def sourceFrames (m : ℕ) (i : World) : Frame (ZMod 2) (Arrays m) :=
  matrixFrame m (sourceMatrix i)

def program {n : ℕ} (m : ℕ) (e : Fin n ≃ Triple) :
    List (FramedCircuit.Instruction World (ZMod 2) (Arrays m)) :=
  Shared50SignedFramed.program e (frames m) (sourceFrames m)

/-- Scalar arithmetic remains exactly the existing reused physical circuit. -/
theorem scalar_erasure {n : ℕ} (m : ℕ) (e : Fin n ≃ Triple) :
    BoundedFramedCircuit.erase (program m e) = Shared50GlobalCircuit.program e :=
  Shared50SignedFramed.scalar_erasure e (frames m) (sourceFrames m)

theorem matrixFrame_change (m : ℕ) (A B : Mat) (f : Arrays m) :
    matrixFrame m B ((matrixFrame m A).symm f) =
      ShearFrame.frame (Matrix.toLin' (reduce m B - reduce m A)) f := by
  rw [matrixFrame,matrixFrame,ShearFrame.frame_change,map_sub]

/-- The complete physical program acts on every array, including dirty scratch. -/
theorem program_identity {n : ℕ} (m : ℕ) (e : Fin n ≃ Triple)
    (hendpoint : ∀ i, reduce m (sinkMatrix i) - reduce m (sourceMatrix (route i)) = 1)
    (stored : World → Arrays m) :
    FramedCircuit.run (program m e) stored =
      fun i => ShearFrame.frame (LinearMap.id : Vector m →ₗ[ZMod m] Vector m) (stored (route i)) := by
  rw [program,Shared50SignedFramed.program_route]
  funext i
  change matrixFrame m (sinkMatrix i)
    ((matrixFrame m (sourceMatrix (route i))).symm (stored (route i))) = _
  rw [matrixFrame_change,hendpoint,Matrix.toLin'_one]

/-- Entrywise form of the routed full address shear. -/
theorem program_apply {n : ℕ} (m : ℕ) (e : Fin n ≃ Triple)
    (hendpoint : ∀ i, reduce m (sinkMatrix i) - reduce m (sourceMatrix (route i)) = 1)
    (stored : World → Arrays m) (i : World) (a : Address m) :
    FramedCircuit.run (program m e) stored i a = stored (route i) (a.1-a.2,a.2) := by
  rw [program_identity m e hendpoint]
  rfl

/-- The actual physical frame pairs match the exact old/new modular matrices. -/
theorem physical_pairs {n : ℕ} (m : ℕ) (e : Fin n ≃ Triple) :
    FramedEdgeTrace.pairs (program m e) =
      (Shared50ModularSchedule.pairs e).map (fun p => (matrixFrame m p.1,matrixFrame m p.2)) := by
  rw [program,Shared50SignedFramed.program_pairs]
  simp only [Shared50ModularSchedule.pairs,Shared50OperatorPairs.pairs,
    Shared50OperatorPairs.boundary,Shared50OperatorPairs.tail,List.map_append,List.map_map,
    Function.comp_def,Shared50ModularOperators.matrix_neg]
  rfl

/-- A field-operation list realizes a physical array edge by an actual address
permutation: values move forward, so array evaluation pulls back by its inverse. -/
def EdgeRealizes (m : ℕ) (edge : Frame (ZMod 2) (Arrays m) × Frame (ZMod 2) (Arrays m))
    (p : List (Swap.Shear.Op Index (ZMod m))) : Prop :=
  ∃ move : Address m ≃ Address m,
    (∀ a, Swap.Shear.run p a = move a) ∧
    ∀ f, edge.2 (edge.1.symm f) = fun a => f (move.symm a)

/-- Admissible reduction connects each ordered field program to its genuine
physical frame edge, using the proved reduction of the rational difference. -/
theorem edge_realizes (m : ℕ) (e : Mat × Mat)
    (p : List (Swap.Shear.Op Index (ZMod m)))
    (h : ModularFrameSchedule.EdgeSpec m e p) :
    EdgeRealizes m (matrixFrame m e.1,matrixFrame m e.2) p := by
  refine ⟨ShearFrame.address (Matrix.toLin' (reduce m (e.2-e.1))),h.run_reduced,?_⟩
  intro f
  rw [matrixFrame_change,← h.reduce_difference]
  rfl

/-- Programs stay in the exact order of the actual physical edge trace. -/
theorem physical_realizes {n : ℕ} (m : ℕ) (e : Fin n ≃ Triple)
    (ps : List (List (Swap.Shear.Op Index (ZMod m))))
    (h : List.Forall₂ (ModularFrameSchedule.EdgeSpec m) (Shared50ModularSchedule.pairs e) ps) :
    List.Forall₂ (EdgeRealizes m) (FramedEdgeTrace.pairs (program m e)) ps := by
  rw [physical_pairs,List.forall₂_map_left_iff]
  exact h.imp (fun e p hp => edge_realizes m e p hp)

/-- One odd prime works at every radix exponent, for the complete finite
address execution and all its physical field programs with the certified cost. -/
theorem exists_prime_execution :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ ∀ b : ℕ,
      (∀ stored : World → Arrays (q^b),
        FramedCircuit.run (program (q^b) Shared50GlobalCircuit.enumeration) stored =
          fun i a => stored (route i) (a.1-a.2,a.2)) ∧
      ∃ ps : List (List (Swap.Shear.Op Index (ZMod (q^b)))),
        List.Forall₂ (ModularFrameSchedule.EdgeSpec (q^b))
          (Shared50ModularSchedule.pairs Shared50GlobalCircuit.enumeration) ps ∧
        List.Forall₂ (EdgeRealizes (q^b))
          (FramedEdgeTrace.pairs (program (q^b) Shared50GlobalCircuit.enumeration)) ps ∧
        (ps.map Swap.Shear.interchanges).sum = Shared50Parameters.s := by
  obtain ⟨q,hq,hodd,_hd,h⟩ := Shared50ModularSchedule.exists_prime_actual
  refine ⟨q,hq,hodd,?_⟩
  intro b
  obtain ⟨_hsource,_hsink,hendpoint,ps,hps,hcount⟩ := h b
  refine ⟨?_,ps,hps,physical_realizes (q^b) Shared50GlobalCircuit.enumeration ps hps,hcount⟩
  intro stored
  funext i a
  exact program_apply (q^b) Shared50GlobalCircuit.enumeration hendpoint stored i a

/-- One fixed prime and one fixed rational control schedule supply the complete
finite modular network at every width, with no new per-width program choice.
Matrix transformations are single field-operation entries here, not tape steps. -/
theorem chosen_certificate (b : ℕ) :
    (∀ stored : World → Arrays (Shared50ModularControl.prime ^ b),
      FramedCircuit.run (program (Shared50ModularControl.prime ^ b) Shared50GlobalCircuit.enumeration) stored =
        fun i a => stored (route i) (a.1-a.2,a.2)) ∧
    List.Forall₂ (EdgeRealizes (Shared50ModularControl.prime ^ b))
      (FramedEdgeTrace.pairs (program (Shared50ModularControl.prime ^ b) Shared50GlobalCircuit.enumeration))
      (Shared50ModularControl.programs (Shared50ModularControl.prime ^ b)) ∧
    ((Shared50ModularControl.programs (Shared50ModularControl.prime ^ b)).map Swap.Shear.interchanges).sum =
      Shared50Parameters.s ∧
    ((Shared50ModularControl.programs (Shared50ModularControl.prime ^ b)).map List.length).sum =
      3 * Shared50Parameters.s + 4 * Shared50ModularControl.edges.length := by
  refine ⟨?_, physical_realizes _ _ _ (Shared50ModularControl.chosen_edge_specs b),
    Shared50ModularControl.interchanges_exact _, Shared50ModularControl.operation_count _⟩
  intro stored
  funext i a
  exact program_apply _ _ (Shared50ModularControl.chosen_endpoint b) stored i a

end
end IntegerMultBounds.Networks.Shared50ModularExecution
