import IntegerMultBounds.Machine.OneSourceCircuit
import IntegerMultBounds.Networks.Shared50GlobalCircuit

/-! The actual Shared50 scalar lists satisfy the physical one-source compiler's
hypothesis. Proofs follow the allocator's layout certificates and list structure;
no enormous concrete instruction list is evaluated or replaced by a new list. -/
namespace IntegerMultBounds.Machine.Shared50XorLists
open Networks OneSourceCircuit
open Circuit NeighborCounts

attribute [local irreducible] SharedPointReplay.circuit SharedPointExecution.code
  Shared50Finite.program Shared50Finite.output Shared50Dirty.pairIndex Shared50Dirty.partialRole

private theorem allocated_xor {ι : Type*} [DecidableEq ι]
    (nodes : List (DisjointCircuit.Node ι)) (outputs : List ℕ) (hv : DisjointCircuit.Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) : IsXor (DAGAllocator.compile nodes outputs).program := by
  intro op hop
  obtain ⟨gate,hgate,hop⟩ := List.mem_flatMap.mp hop
  obtain ⟨layout,hi,ho'⟩ := (DAGAllocator.compile_frontier nodes outputs hv ho).2.2 gate hgate
  rw [DAGAllocator.Gate.program_eq_layout gate layout hi ho'] at hop
  exact layout.program_add op hop

private theorem finite_xor {ι : Type*} [DecidableEq ι]
    (nodes : List (DisjointCircuit.Node ι)) (outputs : List ℕ) (hv : DisjointCircuit.Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (capacity : ℕ)
    (hc : (DAGAllocator.compile nodes outputs).state.next ≤ capacity) :
    IsXor (DAGFiniteCompile.program nodes outputs hv ho capacity hc) := by
  exact OneSourceCircuit.finiteProgram _ _ _ (allocated_xor nodes outputs hv ho)

theorem finite : IsXor Shared50Finite.program := by
  unfold Shared50Finite.program
  exact finite_xor _ _ _ _ _ _

theorem io_load {n : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseIO.load e) :=
  copies _ _ _ (by intros; simp [DirtyLinearCircuit.scratch,DirtyLinearCircuit.x])

theorem io_read {n : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseIO.read e) :=
  copies _ _ _ (by intros; simp [DirtyLinearCircuit.y,DirtyLinearCircuit.scratch])

theorem load {n s : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseInvocation.load (s := s) e) :=
  copies _ _ _ (by intros; simp [side,x])

theorem read {n s : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseInvocation.read (s := s) e) :=
  copies _ _ _ (by intros; simp [y,side])

theorem gather {n a s : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseCentral.gather (a := a) (s := s) e) :=
  copies _ _ _ (by intros; simp [center,x])

theorem scatter {n a s : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseCentral.scatter (a := a) (s := s) e) :=
  copies _ _ _ (by intros; simp [y,center])

theorem forward (n s : ℕ) : IsXor (Shared50SparseInvocation.forward n s) :=
  embed _ finite

theorem backward (n s : ℕ) : IsXor (Shared50SparseInvocation.backward n s) :=
  embed _ (reverse finite)

theorem invocation {n s : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseInvocation.program (s := s) e) := by
  unfold Shared50SparseInvocation.program
  repeat' apply OneSourceCircuit.append
  all_goals first | exact forward _ _ | exact backward _ _ | exact read e | exact load e | exact gather e | exact scatter e

theorem inverse {n s : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseInvocation.inverse (s := s) e) := by
  unfold Shared50SparseInvocation.inverse
  repeat' apply OneSourceCircuit.append
  all_goals first | exact forward _ _ | exact backward _ _ | exact read e | exact load e | exact gather e | exact scatter e

theorem opposite {n s : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseInvocation.opposite (s := s) e) :=
  OneSourceCircuit.rename _ (inverse e)

theorem exchange {n s : ℕ} (e : Fin n ≃ Triple 50) : IsXor (Shared50SparseInvocation.exchange (s := s) e) :=
  append (invocation e) (append (opposite e) (invocation e))

theorem localProgram {n : ℕ} (e : Fin n ≃ Shared50GlobalBudget.Triple) (j : Fin 3) :
    IsXor (Shared50GlobalCircuit.localProgram e j) := by
  unfold Shared50GlobalCircuit.localProgram
  split
  · exact opposite e
  · exact invocation e

theorem globalInvocation {n : ℕ} (e : Fin n ≃ Shared50GlobalBudget.Triple)
    (j : Fin 3) (q : Shared50GlobalBudget.Triple × Shared50GlobalBudget.Triple) :
    IsXor (Shared50GlobalCircuit.invocationProgram e j q) := embed _ (localProgram e j)

theorem globalStage {n : ℕ} (e : Fin n ≃ Shared50GlobalBudget.Triple) (j : Fin 3) :
    IsXor (Shared50GlobalCircuit.stage e j) := by
  intro op hop
  obtain ⟨q,_,hop⟩ := List.mem_flatMap.mp hop
  exact globalInvocation e j q op hop

theorem global {n : ℕ} (e : Fin n ≃ Shared50GlobalBudget.Triple) : IsXor (Shared50GlobalCircuit.program e) :=
  append (append (globalStage e 0) (globalStage e 1)) (globalStage e 2)

theorem global50 : IsXor Shared50GlobalCircuit.program50 := global Shared50GlobalCircuit.enumeration

end IntegerMultBounds.Machine.Shared50XorLists
