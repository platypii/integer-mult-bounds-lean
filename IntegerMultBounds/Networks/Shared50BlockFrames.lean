import IntegerMultBounds.Networks.Shared50LabeledInvocation
import IntegerMultBounds.Networks.Shared50SparseInvocation

/-! Actual sparse scalar blocks use a common frame on each gate's precise
incidences. No dense zero-coefficient terms or assumed attachment contract is
used in these frame-commutation theorems. -/

namespace IntegerMultBounds.Networks.Shared50BlockFrames

open Circuit FramedCircuit

section Generic
variable {ι κ L M : Type*} [DecidableEq ι] [DecidableEq κ]
  [AddCommGroup M] [Module (ZMod 2) M]

/-- Each actual scalar gate has one label on all of its incidences. -/
def Uniform (labels : ι → L) (p : Program ι (ZMod 2)) : Prop :=
  ∀ gate ∈ p, ∃ common, ∀ i ∈ touched gate, labels i = common

omit [DecidableEq ι] in
theorem uniform_append (labels : ι → L) (p q : Program ι (ZMod 2))
    (hp : Uniform labels p) (hq : Uniform labels q) : Uniform labels (p++q) := by
  intro gate hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hp gate hg
  · exact hq gate hg

/-- A fixed label profile commutes with the actual complete scalar block. -/
theorem module_invariant (frameOf : L → Frame (ZMod 2) M) (labels : ι → L)
    (p : Program ι (ZMod 2)) (hp : Uniform labels p) (state : ι → M) :
    moduleRun p (encode (fun i => frameOf (labels i)) state) =
      encode (fun i => frameOf (labels i)) (moduleRun p state) := by
  induction p generalizing state with
  | nil => rfl
  | cons gate p ih =>
    obtain ⟨common,hc⟩ := hp gate (by simp)
    rw [moduleRun_cons,gate_invariant gate _ (frameOf common) (fun i hi => congrArg frameOf (hc i hi)),
      ih (fun gate hg => hp gate (by simp [hg]))]
    rfl

omit [DecidableEq ι] [DecidableEq κ] in
/-- A scratch-only program is common-frame when that physical bank is uniform. -/
theorem embed_uniform (labels : κ → L) (e : ι ↪ κ) (common : L)
    (hc : ∀ i, labels (e i) = common) (p : Program ι (ZMod 2)) :
    Uniform labels (GlobalCircuit.embed e p) := by
  intro gate hg
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hg
  refine ⟨common,?_⟩
  intro i hi
  simp only [touched,GlobalCircuit.embedGate,List.map_map,List.mem_cons,List.mem_map] at hi
  rcases hi with rfl | ⟨term,_,rfl⟩
  · exact hc g.target
  · exact hc term.1

omit [DecidableEq ι] in
/-- Each emitted copy touches exactly its destination and its one true source. -/
theorem copies_uniform {A B : Type*} (labels : ι → L) (dst : A → ι) (src : B → ι)
    (entries : List (A × B)) (h : ∀ p ∈ entries, labels (dst p.1) = labels (src p.2)) :
    Uniform labels (SparseCircuit.copies dst src entries) := by
  intro gate hg
  obtain ⟨entry,he,rfl⟩ := List.mem_map.mp hg
  refine ⟨labels (dst entry.1),?_⟩
  intro i hi
  have hi' : i = dst entry.1 ∨ i = src entry.2 := by simpa [touched,ReversibleFanout.add] using hi
  rcases hi' with rfl | rfl
  · rfl
  · exact (h entry he).symm
end Generic

open scoped TensorProduct
open MotifLabels Shared50StageFrames Shared50LabeledInvocation NeighborCounts
variable {n s : ℕ} {E H : Type*} [AddCommGroup E] [Module ℚ E]
  [AddCommGroup H] [Module ℚ H]

attribute [local irreducible] SharedPointExecution.code SharedPointReplay.circuit Shared50Finite.program

/-- Both early scratch computation directions use the common stage frame. -/
theorem early_side (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (p : Program (Fin 509194) (ZMod 2)) :
    Uniform (early (s := s) g q e)
      (GlobalCircuit.embed (Shared50Invocation.sideEmbedding n 509194 50 s) p) :=
  embed_uniform _ _ (low g q) (fun _ => rfl) p

theorem early_read (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (early (s := s) g q e) (Shared50SparseInvocation.read e) :=
  copies_uniform _ _ _ _ (fun _ _ => rfl)

theorem early_scatter (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (early (s := s) g q e) (Shared50SparseCentral.scatter e) :=
  copies_uniform _ _ _ _ (fun _ _ => rfl)

/-- Source-loading incidences use the proved physical source label. -/
theorem loaded_load (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (loaded (s := s) g q e) (Shared50SparseInvocation.load e) := by
  apply copies_uniform
  intro entry he
  obtain ⟨source,_,rfl⟩ := List.mem_map.mp he
  exact loaded_source_frame g q e source

theorem gathered_gather (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (gathered (n := n) (s := s) g q) (Shared50SparseCentral.gather e) :=
  copies_uniform _ _ _ _ (fun _ _ => rfl)

theorem returned_scatter (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (returned (n := n) (s := s) g q) (Shared50SparseCentral.scatter e) :=
  copies_uniform _ _ _ _ (fun _ _ => rfl)

/-- Readout incidences use the proved target owner of each physical partial output. -/
theorem readout_read (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (readout (s := s) g q e) (Shared50SparseInvocation.read e) := by
  apply copies_uniform
  intro entry he
  obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp he
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp hi
  exact (readout_source_frame g q e i c).symm

theorem output_side (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50)
    (p : Program (Fin 509194) (ZMod 2)) :
    Uniform (output (s := s) g q e)
      (GlobalCircuit.embed (Shared50Invocation.sideEmbedding n 509194 50 s) p) :=
  embed_uniform _ _ (high g q) (fun _ => rfl) p

theorem output_gather (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (output (s := s) g q e) (Shared50SparseCentral.gather e) :=
  copies_uniform _ _ _ _ (fun _ _ => rfl)

theorem output_load (g : Geometry ℚ E Factor) (q : H) (e : Fin n ≃ Triple 50) :
    Uniform (output (s := s) g q e) (Shared50SparseInvocation.load e) :=
  copies_uniform _ _ _ _ (fun _ _ => rfl)

end IntegerMultBounds.Networks.Shared50BlockFrames
