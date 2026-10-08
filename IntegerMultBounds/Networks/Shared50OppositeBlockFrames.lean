import IntegerMultBounds.Networks.Shared50BlockFrames
import IntegerMultBounds.Networks.Shared50OppositeLabels

/-! Common-frame proofs for the actual swapped sparse blocks in the opposite
invocation. The backward middle computation is handled by its physical frames. -/

namespace IntegerMultBounds.Networks.Shared50OppositeBlockFrames

open Circuit FramedCircuit Shared50BlockFrames

section Generic
variable {ι κ A B : Type*} [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem rename_copies (e : ι ≃ κ) (dst : A → ι) (src : B → ι) (entries : List (A × B)) :
    rename e (SparseCircuit.copies dst src entries) =
      SparseCircuit.copies (fun i => e (dst i)) (fun i => e (src i)) entries := by
  simp only [rename,SparseCircuit.copies,List.map_map,Function.comp_def,Gate.rename,ReversibleFanout.add,List.map_cons,List.map_nil]
end Generic

open scoped TensorProduct
open MotifLabels Shared50StageFrames Shared50LabeledInvocation Shared50OppositeLabels NeighborCounts
variable {n s : ℕ} {E H : Type*} [AddCommGroup E] [Module ℚ E]
  [AddCommGroup H] [Module ℚ H]

attribute [local irreducible] SharedPointExecution.code SharedPointReplay.circuit Shared50Finite.program

/-- Actual exchanged input copies, from physical Y to side scratch. -/
def load (e : Fin n ≃ Triple 50) : Program (Wire n s) (ZMod 2) :=
  rename (exchangeRoles n 509194 50 s) (Shared50SparseInvocation.load e)

/-- Actual exchanged output copies, from side scratch to physical X. -/
def read (e : Fin n ≃ Triple 50) : Program (Wire n s) (ZMod 2) :=
  rename (exchangeRoles n 509194 50 s) (Shared50SparseInvocation.read e)

def gather (e : Fin n ≃ Triple 50) : Program (Wire n s) (ZMod 2) :=
  rename (exchangeRoles n 509194 50 s) (Shared50SparseCentral.gather e)

def scatter (e : Fin n ≃ Triple 50) : Program (Wire n s) (ZMod 2) :=
  rename (exchangeRoles n 509194 50 s) (Shared50SparseCentral.scatter e)

theorem rename_side (p : Program (Fin 509194) (ZMod 2)) :
    rename (exchangeRoles n 509194 50 s)
      (GlobalCircuit.embed (Shared50Invocation.sideEmbedding n 509194 50 s) p) =
      GlobalCircuit.embed (Shared50Invocation.sideEmbedding n 509194 50 s) p := by
  simp only [rename,GlobalCircuit.embed,List.map_map]
  congr 1
  funext gate
  cases gate
  simp only [Function.comp_apply,Gate.rename,GlobalCircuit.embedGate,List.map_map]
  rfl

theorem early_load (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (early (s := s) g q e) (load e) := by
  rw [load,Shared50SparseInvocation.load,rename_copies]
  exact copies_uniform _ _ _ _ (fun _ _ => rfl)

theorem early_gather (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (early (s := s) g q e) (gather e) := by
  rw [gather,Shared50SparseCentral.gather,rename_copies]
  exact copies_uniform _ _ _ _ (fun _ _ => rfl)

theorem injected_read (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (injected (s := s) g q e) (read e) := by
  rw [read,Shared50SparseInvocation.read,rename_copies]
  apply copies_uniform
  intro entry he
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp he
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hi
  exact (injected_source_frame g q e i c).symm

theorem gathered_scatter (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (reverseGathered (n := n) (s := s) g q) (scatter e) := by
  rw [scatter,Shared50SparseCentral.scatter,rename_copies]
  exact copies_uniform _ _ _ _ (fun _ _ => rfl)

theorem returned_gather (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (reverseReturned (n := n) (s := s) g q) (gather e) := by
  rw [gather,Shared50SparseCentral.gather,rename_copies]
  exact copies_uniform _ _ _ _ (fun _ _ => rfl)

theorem drained_load (g : Geometry ℚ E Factor) (hcurrent : g.current = Labels.rational 50)
    (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (drained (s := s) g q e) (load e) := by
  rw [load,Shared50SparseInvocation.load,rename_copies]
  apply copies_uniform
  intro entry he
  obtain ⟨source,_,rfl⟩ := List.mem_map.mp he
  exact drained_source_frame g hcurrent q e source

theorem output_scatter (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (output (s := s) g q e) (scatter e) := by
  rw [scatter,Shared50SparseCentral.scatter,rename_copies]
  exact copies_uniform _ _ _ _ (fun _ _ => rfl)

theorem output_read (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (output (s := s) g q e) (read e) := by
  rw [read,Shared50SparseInvocation.read,rename_copies]
  exact copies_uniform _ _ _ _ (fun _ _ => rfl)

end IntegerMultBounds.Networks.Shared50OppositeBlockFrames
