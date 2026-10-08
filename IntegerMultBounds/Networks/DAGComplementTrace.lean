import IntegerMultBounds.Networks.DAGFramedExecution

/-! Exact complementary reversal of the allocated forward frame trace.
Forward old labels are recorded, so reversing restores their complements even
at identity pivots and repeated incidences. Inverse scalar gates keep their
original event boundaries and execute in complemented node frames. This does
not assemble the surrounding correction motif or its sink/global rank joins. -/

namespace IntegerMultBounds.Networks.DAGComplementTrace

section ReverseUpdates
variable {ι L M : Type*} [DecidableEq ι]

/-- Undo each actual label assignment in reverse order, mapping both its old
and new labels by `dual`. For orthogonal complements this reverses inclusion. -/
def undo (dual : L → M) : (ι → L) → List (ι × L) → List (ι × M)
  | _, [] => []
  | current, (i,next)::rest =>
    undo dual (Function.update current i next) rest ++ [(i,dual (current i))]

/-- Complementary reversal has exact endpoint profiles on every role. -/
theorem undo_finish (dual : L → M) (current : ι → L) (xs : List (ι × L)) :
    RankTrace.finish (fun i => dual (RankTrace.finish current xs i)) (undo dual current xs) =
      fun i => dual (current i) := by
  induction xs generalizing current with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨i,next⟩ := p
    simp only [undo,RankTrace.finish,RankTrace.finish_append,ih]
    funext j
    by_cases hj : j = i <;> simp [hj]

/-- The actual reversed edge list is precisely the reversed forward edge list
with both endpoints mapped and exchanged, including repeated identity edges. -/
theorem undo_edges (dual : L → M) (current : ι → L) (xs : List (ι × L)) :
    RankTrace.edges (fun i => dual (RankTrace.finish current xs i)) (undo dual current xs) =
      ((RankTrace.edges current xs).reverse.map fun p => (dual p.2,dual p.1)) := by
  induction xs generalizing current with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨i,next⟩ := p
    simp only [undo,RankTrace.finish,RankTrace.edges_append,ih,undo_finish,
      RankTrace.edges,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,Function.update_self]

/-- Event boundaries are preserved: undo a later event's updates first, then
undo the earlier event from its recorded starting profile. -/
theorem undo_append (dual : L → M) (current : ι → L) (xs ys : List (ι × L)) :
    undo dual current (xs ++ ys) =
      undo dual (RankTrace.finish current xs) ys ++ undo dual current xs := by
  induction xs generalizing current with
  | nil => simp [undo,RankTrace.finish]
  | cons p rest ih =>
    obtain ⟨i,next⟩ := p
    simp only [List.cons_append,undo,RankTrace.finish,ih,List.append_assoc]

/-- Erasing the trace transformation preserves the exact number of incidences. -/
theorem undo_length (dual : L → M) (current : ι → L) (xs : List (ι × L)) :
    (undo dual current xs).length = xs.length := by
  induction xs generalizing current with
  | nil => rfl
  | cons p rest ih => simp [undo,ih]
end ReverseUpdates

section Complement
variable {ι K V : Type*} [DecidableEq ι] [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- Orthogonal complementation turns reversed increasing edges into increasing
edges. Merely reversing their order would instead make them decrease. -/
theorem complement_increasing (B : LinearMap.BilinForm K V) (current : ι → Submodule K V)
    (xs : List (ι × Submodule K V))
    (hi : ∀ p ∈ RankTrace.edges current xs, p.1 ≤ p.2) :
    ∀ p ∈ RankTrace.edges (fun i => B.orthogonal (RankTrace.finish current xs i))
      (undo B.orthogonal current xs), p.1 ≤ p.2 := by
  intro p hp
  rw [undo_edges] at hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact B.orthogonal_le (hi q (List.mem_reverse.mp hq))

/-- Ambient nondegeneracy transfers both endpoints of every reversed frame
edge to their orthogonal complements. -/
theorem complement_nondegenerate (B : LinearMap.BilinForm K V) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (current : ι → Submodule K V) (xs : List (ι × Submodule K V))
    (he : ∀ p ∈ RankTrace.edges current xs,
      (B.restrict p.1).Nondegenerate ∧ (B.restrict p.2).Nondegenerate) :
    ∀ p ∈ RankTrace.edges (fun i => B.orthogonal (RankTrace.finish current xs i))
      (undo B.orthogonal current xs),
      (B.restrict p.1).Nondegenerate ∧ (B.restrict p.2).Nondegenerate := by
  intro p hp
  rw [undo_edges] at hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  have hq' := he q (List.mem_reverse.mp hq)
  exact ⟨ProjectionRank.orthogonal_nondegenerate B hs hn q.2 hq'.2,
    ProjectionRank.orthogonal_nondegenerate B hs hn q.1 hq'.1⟩

theorem complement_loss_zero (B : LinearMap.BilinForm K V) (current : ι → Submodule K V)
    (xs : List (ι × Submodule K V))
    (hi : ∀ p ∈ RankTrace.edges current xs, p.1 ≤ p.2) :
    RankTrace.loss (fun U : Submodule K V => Module.finrank K U)
      (fun i => B.orthogonal (RankTrace.finish current xs i)) (undo B.orthogonal current xs) = 0 := by
  unfold RankTrace.loss
  apply List.sum_eq_zero
  intro value hv
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hv
  exact Nat.sub_eq_zero_of_le (Submodule.finrank_mono (complement_increasing B current xs hi p hp))
end Complement

section ActualDAG
open DisjointCircuit DAGSupportTrace
variable {α : Type*} [DecidableEq α] {h : ℕ}

/-- Actual forward span-label profile, before physical event alignment. -/
def inputLabels (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h)) :
    ℕ → Submodule ℚ (Fin h → ℚ) :=
  fun i => FanoutFrames.label triples (initialSupports nodes outputs i)

/-- The reversed computation starts at complements of the actual forward
terminal profile, not complements of an assumed output-label annotation. -/
def reverseInput (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h)) :
    ℕ → Submodule ℚ (Fin h → ℚ) :=
  fun i => (Labels.rational h).orthogonal
    (RankTrace.finish (inputLabels nodes outputs triples) (updates (events nodes outputs) triples) i)

def reverseOutput (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h)) :
    ℕ → Submodule ℚ (Fin h → ℚ) :=
  fun i => (Labels.rational h).orthogonal (inputLabels nodes outputs triples i)

def reverseTrace (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h)) :
    List (ℕ × Submodule ℚ (Fin h → ℚ)) :=
  undo (Labels.rational h).orthogonal (inputLabels nodes outputs triples) (updates (events nodes outputs) triples)

theorem reverse_endpoints (nodes : List (Node α)) (outputs : List ℕ) (triples : α → Finset (Fin h)) :
    RankTrace.finish (reverseInput nodes outputs triples) (reverseTrace nodes outputs triples) =
      reverseOutput nodes outputs triples :=
  undo_finish _ _ _

theorem reverse_increasing (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (triples : α → Finset (Fin h)) :
    ∀ p ∈ RankTrace.edges (reverseInput nodes outputs triples) (reverseTrace nodes outputs triples),
      p.1 ≤ p.2 :=
  complement_increasing _ _ _ (events_increasing nodes outputs hv ho triples)

theorem reverse_loss_zero (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (triples : α → Finset (Fin h)) :
    RankTrace.loss (fun U : Submodule ℚ (Fin h → ℚ) => Module.finrank ℚ U)
      (reverseInput nodes outputs triples) (reverseTrace nodes outputs triples) = 0 :=
  complement_loss_zero _ _ _ (events_increasing nodes outputs hv ho triples)

/-- The rational ambient form must be nondegenerate for complement labels;
`h ≠ 9` is the exact additional dimension premise (satisfied at fifty). -/
theorem reverse_nondegenerate (nodes : List (Node α)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (triples : α → Finset (Fin h)) (hh : h ≠ 9)
    (hs : ∀ node ∈ nodes, ∃ common : Fin h,
      ∀ a ∈ node.support, (triples a).card = 3 ∧ common ∈ triples a) :
    ∀ p ∈ RankTrace.edges (reverseInput nodes outputs triples) (reverseTrace nodes outputs triples),
      ((Labels.rational h).restrict p.1).Nondegenerate ∧
      ((Labels.rational h).restrict p.2).Nondegenerate :=
  complement_nondegenerate _ ⟨Labels.form_symm (1 / 9)⟩ (Labels.rational_nondegenerate hh) _ _
    (events_nondegenerate nodes outputs hv ho triples hs)

/-- Inverse scalar instructions reverse both event order and each event's
literal instruction list. Event boundaries, including identities, are retained. -/
def inversePrograms (es : List (Event α)) : Circuit.Program ℕ (ZMod 2) :=
  es.reverse.flatMap (fun event => event.gate.program.reverse)

omit [DecidableEq α] in
theorem inversePrograms_eq_reverse (es : List (Event α)) :
    inversePrograms es = (es.flatMap fun event => event.gate.program).reverse := by
  induction es with
  | nil => rfl
  | cons event es ih =>
      simpa only [inversePrograms,List.reverse_cons,List.flatMap_append,
        List.flatMap_cons,List.flatMap_nil,List.append_nil,List.reverse_append] using
        congrArg (fun p => p ++ event.gate.program.reverse) ih

omit [DecidableEq α] in
theorem scalar_erasure (nodes : List (Node α)) (outputs : List ℕ) :
    inversePrograms (events nodes outputs) = (DAGAllocator.compile nodes outputs).program.reverse := by
  rw [inversePrograms_eq_reverse,DAGFramedExecution.scalar_erasure]

end ActualDAG
end IntegerMultBounds.Networks.DAGComplementTrace
