import IntegerMultBounds.Networks.DAGValueTransfer

/-! Certified finite locations and input labels for actual allocator source
entries. Extracting an input label uses its proved input-node shape, never a
default label or identification of repeated semantic inputs. -/

namespace IntegerMultBounds.Networks.DAGSourceRoles

open DisjointCircuit DAGAllocator

variable {ι : Type*}

theorem compileFrom_next_mono (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι))
    (hlive : ∀ i ∈ active, users all active outputs i ≠ []) :
    state.next ≤ (compileFrom all active outputs state offset nodes).state.next := by
  induction nodes generalizing state offset with
  | nil => exact le_refl _
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · have hh := ih (allocate state offset node (users all active outputs offset)).state (offset+1)
      have hc := allocate_count state offset node _ (hlive offset ha)
      have hp := List.length_pos_iff.mpr (hlive offset ha)
      simp only [compileFrom, ha, ↓reduceIte]
      omega
    · simpa only [compileFrom, ha, ↓reduceIte] using ih state (offset+1)

theorem compileFrom_sources_bound (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι))
    (hlive : ∀ i ∈ active, users all active outputs i ≠ []) :
    ∀ entry ∈ (compileFrom all active outputs state offset nodes).sources,
      entry.2 < (compileFrom all active outputs state offset nodes).state.next := by
  induction nodes generalizing state offset with
  | nil => simp [compileFrom]
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · simp only [compileFrom, ha, ↓reduceIte]
      intro entry he
      rcases List.mem_append.mp he with he | he
      · have hh := compileFrom_next_mono all active outputs
          (allocate state offset node (users all active outputs offset)).state (offset+1) nodes hlive
        have hc := allocate_count state offset node _ (hlive offset ha)
        have hp := List.length_pos_iff.mpr (hlive offset ha)
        cases hk : node.kind with
        | add l r => simp [allocate, hk] at he
        | input label =>
          have he' : entry = (offset,state.next) := by simpa [allocate, hk] using he
          subst entry
          simp only [sourceCount, hk] at hc
          omega
      · exact ih _ _ entry he
    · simpa only [compileFrom, ha, ↓reduceIte] using ih state (offset+1)

theorem sources_bound (nodes : List (Node ι)) (outputs : List ℕ) :
    ∀ entry ∈ (compile nodes outputs).sources, entry.2 < (compile nodes outputs).state.next :=
  compileFrom_sources_bound nodes (DisjointPruning.mark nodes outputs.toFinset) outputs ⟨0,[]⟩ 0 nodes
    (fun i hi => users_mark_nonempty nodes outputs i hi)

theorem source_node (nodes : List (Node ι)) (outputs : List ℕ) (entry : ℕ × ℕ)
    (he : entry ∈ (compile nodes outputs).sources) :
    ∃ hi : entry.1 < nodes.length, ∃ label, nodes[entry.1].kind = .input label := by
  obtain ⟨j,hj,label,heq,hkind⟩ := DAGValueTransfer.compileFrom_source_mem nodes
    (DisjointPruning.mark nodes outputs.toFinset) outputs ⟨0,[]⟩ 0 nodes entry he
  simp only [Nat.zero_add] at heq
  subst j
  exact ⟨hj,label,hkind⟩

/-- Read the actual source node's input label; the impossible addition branch
is excluded by the allocator's source-entry theorem. -/
def label (nodes : List (Node ι)) (outputs : List ℕ) (entry : ℕ × ℕ)
    (he : entry ∈ (compile nodes outputs).sources) : ι :=
  let hi := (source_node nodes outputs entry he).choose
  match hk : nodes[entry.1].kind with
  | .input value => value
  | .add _ _ => False.elim (by
      obtain ⟨value,hvalue⟩ := (source_node nodes outputs entry he).choose_spec
      rw [hk] at hvalue
      contradiction)

theorem label_kind (nodes : List (Node ι)) (outputs : List ℕ) (entry : ℕ × ℕ)
    (he : entry ∈ (compile nodes outputs).sources) :
    (nodes[entry.1]'(source_node nodes outputs entry he).choose).kind = .input (label nodes outputs entry he) := by
  unfold label
  dsimp only
  split <;> rename_i hk
  · exact hk
  · obtain ⟨value,hvalue⟩ := (source_node nodes outputs entry he).choose_spec
    rw [hk] at hvalue
    contradiction

theorem sourceInput_label (nodes : List (Node ι)) (outputs : List ℕ) (entry : ℕ × ℕ)
    (he : entry ∈ (compile nodes outputs).sources) (input : ι → ZMod 2) :
    DAGValueTransfer.sourceInput nodes input entry.1 = input (label nodes outputs entry he) := by
  have hi := (source_node nodes outputs entry he).choose
  simp only [DAGValueTransfer.sourceInput, List.getElem?_eq_getElem hi,
    label_kind nodes outputs entry he]

/-- Source preloading as a literal sum over actual source entries. -/
theorem initial_as_sum (sources : List (ℕ × ℕ)) (value : ℕ → ZMod 2) (role : ℕ) :
    DAGValueTransfer.initial sources value role =
      (sources.map (fun entry => if entry.2 = role then value entry.1 else 0)).sum := by
  induction sources with
  | nil => rfl
  | cons entry sources ih =>
    rcases entry with ⟨node, source⟩
    rw [DAGValueTransfer.initial_cons, ih, List.map_cons, List.sum_cons]

end IntegerMultBounds.Networks.DAGSourceRoles
