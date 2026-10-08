import IntegerMultBounds.Networks.Shared50Finite
import IntegerMultBounds.Networks.DirtyLinearCircuit

/-! Dirty-scratch execution of the actual fifty-point shared circuit. Explicit
input and readout matrices connect its physical roles to triple data banks.
These dense matrix wrappers establish semantics, not a rank or runtime budget. -/

namespace IntegerMultBounds.Networks.Shared50Dirty

open DisjointCircuit NeighborCounts SharedPointReplay Circuit

attribute [local irreducible] SharedPointReplay.circuit Shared50Finite.program
  SharedPointExecution.code Paired49Certificate.nodes Certificates.Paired49.outputs
  Certificates.Paired49.entries Certificates.Paired49.bank

section SourceLoading
variable {ι : Type*} [DecidableEq ι] {n : ℕ}

private theorem sourceInput_basis (nodes : List (Node ι)) (e : Fin n ≃ ι)
    (X : Fin n → ZMod 2) (index : ℕ) :
    (∑ i, DAGValueTransfer.sourceInput nodes (fun label => if label = e i then 1 else 0) index * X i) =
      DAGValueTransfer.sourceInput nodes (fun label => X (e.symm label)) index := by
  unfold DAGValueTransfer.sourceInput
  cases hn : nodes[index]? with
  | none => simp
  | some node =>
    cases hk : node.kind with
    | add l r => simp [hk]
    | input label =>
      have he (i : Fin n) : label = e i ↔ i = e.symm label := by
        constructor
        · intro h; simpa using (congrArg e.symm h).symm
        · intro h; rw [h, e.apply_symm_apply]
      simp [hk, he]

private theorem initial_basis (nodes : List (Node ι)) (sources : List (ℕ × ℕ))
    (e : Fin n ≃ ι) (X : Fin n → ZMod 2) (role : ℕ) :
    (∑ i, DAGValueTransfer.initial sources
      (DAGValueTransfer.sourceInput nodes (fun label => if label = e i then 1 else 0)) role * X i) =
      DAGValueTransfer.initial sources
        (DAGValueTransfer.sourceInput nodes (fun label => X (e.symm label))) role := by
  induction sources with
  | nil => simp
  | cons entry rest ih =>
    rcases entry with ⟨index, source⟩
    by_cases he : source = role
    · simp only [DAGValueTransfer.initial_cons, he, ↓reduceIte, add_mul, Finset.sum_add_distrib,
        sourceInput_basis, ih]
    · simp only [DAGValueTransfer.initial_cons, he, ↓reduceIte, zero_add, ih]

end SourceLoading

/-- A pair index selected by finite minimum search, with certified existence. -/
def pairIndex (c : Fin 50) (T : Triple 50) (hc : c ∈ T.val) : Fin 1176 :=
  (Finset.univ.filter (fun j => embedding c j = T)).min' (by
    obtain ⟨j, hj⟩ := SharedPointOutputMap.source_covers 49 c T hc
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)

theorem pairIndex_spec (c : Fin 50) (T : Triple 50) (hc : c ∈ T.val) :
    embedding c (pairIndex c T hc) = T := by
  unfold pairIndex
  exact (Finset.mem_filter.mp (Finset.min'_mem (Finset.univ.filter (fun j : Fin 1176 => embedding c j = T)) _)).2

/-- The finite physical output register for one of a target's three common points. -/
def partialRole (T : Triple 50) (c : {c : Fin 50 // c ∈ T.val}) : Fin 509194 :=
  Shared50Finite.output c.val (pairIndex c.val T c.property)

attribute [local irreducible] pairIndex Shared50Finite.output

theorem partialRole_injective (T : Triple 50) : Function.Injective (partialRole T) := by
  intro c d he
  dsimp only [partialRole] at he
  have hh := @Shared50Finite.output_injective
    (c.val, pairIndex c.val T c.property) (d.val, pairIndex d.val T d.property) he
  exact Subtype.ext (congrArg Prod.fst hh)

section Matrices
variable {n : ℕ}

/-- Basis columns of the actual source-loader, including its exact physical
source-role placement and zero values on all other roles. -/
def inputMatrix (e : Fin n ≃ Triple 50) : Fin 509194 → Fin n → ZMod 2 :=
  fun role i => Shared50Finite.initial (fun T => if T = e i then 1 else 0) role

theorem inputMatrix_mv (e : Fin n ≃ Triple 50) (X : Fin n → ZMod 2) :
    mv (inputMatrix e) X = Shared50Finite.initial (fun T => X (e.symm T)) := by
  funext role
  exact initial_basis circuit.nodes SharedPointExecution.code.sources e X role.val

/-- Add exactly the three allocated partial-output registers for each target. -/
def readoutMatrix (e : Fin n ≃ Triple 50) : Fin n → Fin 509194 → ZMod 2 :=
  fun i role => ∑ c : {c : Fin 50 // c ∈ (e i).val}, if partialRole (e i) c = role then 1 else 0

theorem readoutMatrix_mv (e : Fin n ≃ Triple 50) (state : Fin 509194 → ZMod 2) (i : Fin n) :
    mv (readoutMatrix e) state i =
      ∑ c : {c : Fin 50 // c ∈ (e i).val}, state (partialRole (e i) c) := by
  simp only [mv, readoutMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp

/-- The intersection-one map, indexed by the chosen finite triple enumeration. -/
def neighborMap (e : Fin n ≃ Triple 50) (X : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  fun i => ∑ T : Triple 50, if BitNeighbor T (e i) then X (e.symm T) else 0

theorem partialRole_value (input : Triple 50 → ZMod 2) (T : Triple 50)
    (c : {c : Fin 50 // c ∈ T.val}) :
    run Shared50Finite.program (Shared50Finite.initial input) (partialRole T c) =
      SharedPointMap.sharedOutput c.val T input := by
  have hh := Shared50Finite.run_output input c.val (pairIndex c.val T c.property)
  rw [pairIndex_spec] at hh
  simpa only [partialRole, supportSum, Finset.sum_filter, SharedPointMap.sharedOutput] using hh

/-- The real shared program, initialized at its real source roles and read at
its three real output roles per triple, computes the full neighbor map. -/
theorem readout_execution (e : Fin n ≃ Triple 50) (X : Fin n → ZMod 2) :
    mv (readoutMatrix e) (run Shared50Finite.program (mv (inputMatrix e) X)) = neighborMap e X := by
  rw [inputMatrix_mv]
  funext i
  rw [readoutMatrix_mv]
  simp_rw [partialRole_value]
  exact SharedPointMap.sum_shared_eq_neighbors (e i) (fun T => X (e.symm T))

/-- The actual shared finite circuit and its literal reversal inside the
concrete dirty-scratch cancellation wrapper. -/
def program (e : Fin n ≃ Triple 50) : Program (DirtyLinearCircuit.Register n 509194) (ZMod 2) :=
  DirtyLinearCircuit.program Shared50Finite.program Shared50Finite.program.reverse
    (inputMatrix e) (readoutMatrix e)

/-- Every scratch register is restored, even when it starts dirty. The two
triple data banks undergo precisely the intersection-one shear. -/
theorem program_run (e : Fin n ≃ Triple 50) (X Y : Fin n → ZMod 2) (S : Fin 509194 → ZMod 2) :
    run (program e) (DirtyLinearCircuit.contents X Y S) =
      DirtyLinearCircuit.contents X (Y + neighborMap e X) S := by
  rw [program, DirtyLinearCircuit.program_run _ _ _ _ Shared50Finite.reverse_run, readout_execution]

end Matrices

end IntegerMultBounds.Networks.Shared50Dirty
