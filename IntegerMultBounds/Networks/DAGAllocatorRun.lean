import IntegerMultBounds.Networks.DAGAllocatorFrontier

/-! Induction over the actual allocator execution. The schedule hypotheses
concern only the original consumer wiring, never a supplied allocator result. -/

namespace IntegerMultBounds.Networks.DAGAllocator

open DisjointCircuit

/-- Every actual input port was produced by an earlier node. -/
def EarlyInputs {ι : Type*} (wires : Wiring) (index : ℕ) (node : Node ι) : Prop :=
  ∀ port ∈ (parentPorts index node).map Prod.snd,
    ∃ owner, owner < index ∧ (owner,port) ∈ wires

def Inactive (wires : Wiring) (index : ℕ) : Prop :=
  (∀ port, (index,port) ∉ wires) ∧ (∀ owner right, (owner,.gate index right) ∉ wires)

/-- Original topological wiring conditions for a suffix of the actual loop. -/
def ScheduledFrom {ι : Type*} (wires : Wiring) (active : Finset ℕ) : ℕ → List (Node ι) → Prop
  | _, [] => True
  | index, node :: nodes =>
    (index ∈ active → EarlyInputs wires index node ∧ consumers wires index ≠ []) ∧
    (index ∉ active → Inactive wires index) ∧ ScheduledFrom wires active (index+1) nodes

theorem inputsReady_domain {ι : Type*} (wires : Wiring) (state : State) (index : ℕ)
    (node : Node ι) (hd : Domain wires index state) (hi : EarlyInputs wires index node) :
    InputsReady state index node := by
  cases node with
  | mk kind support =>
    cases kind with
    | input label => trivial
    | add left right =>
      constructor
      · exact (hd (.gate index false)).mpr ⟨hi _ (by simp [parentPorts]), le_refl _⟩
      · exact (hd (.gate index true)).mpr ⟨hi _ (by simp [parentPorts]), le_refl _⟩

/-- Skipping an inactive node changes no pending ports; the concrete wiring
has neither a producer nor a consumer at that node. -/
theorem skip_domain (wires : Wiring) (state : State) (index : ℕ)
    (hd : Domain wires index state) (hi : Inactive wires index) : Domain wires (index+1) state := by
  intro port
  rw [hd]
  constructor
  · rintro ⟨⟨owner, ho, hw⟩, hp⟩
    refine ⟨⟨owner, by omega, hw⟩, ?_⟩
    cases port with
    | output n => trivial
    | gate target right =>
      change index ≤ target at hp
      change index+1 ≤ target
      have hne : target ≠ index := by rintro rfl; exact hi.2 owner right hw
      omega
  · rintro ⟨⟨owner, ho, hw⟩, hp⟩
    have hne : owner ≠ index := by rintro rfl; exact hi.1 port hw
    refine ⟨⟨owner, by omega, hw⟩, ?_⟩
    cases port with
    | output n => trivial
    | gate target right => change index+1 ≤ target at hp; change index ≤ target; omega

def Gate.HasLayout (gate : Gate) : Prop :=
  ∃ layout : ReversibleFanout.Layout ℕ, layout.inputs = gate.inputs ∧ layout.outputs = gate.outputs

/-- The real loop preserves the live-port invariant and emits only concrete
reversible fanout layouts. This does not run or assume a layout checker. -/
theorem compileFrom_frontier {ι : Type*} (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι))
    (hw : WiringValid (gatePortsFrom active 0 all ++ requestedPorts outputs))
    (hs : ScheduledFrom (gatePortsFrom active 0 all ++ requestedPorts outputs) active offset nodes)
    (hf : Frontier state) (hd : Domain (gatePortsFrom active 0 all ++ requestedPorts outputs) offset state) :
    let code := compileFrom all active outputs state offset nodes
    Frontier code.state ∧
      Domain (gatePortsFrom active 0 all ++ requestedPorts outputs) (offset+nodes.length) code.state ∧
      state.next ≤ code.state.next ∧ ∀ gate ∈ code.gates, gate.HasLayout := by
  induction nodes generalizing state offset with
  | nil => exact ⟨hf, by simpa [compileFrom] using hd, le_refl _, by simp [compileFrom]⟩
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · obtain ⟨hearly, hlive⟩ := hs.1 ha
      have hin := inputsReady_domain _ state offset node hd hearly
      have hstep := allocate_frontier_domain _ offset state node hw hd hf hin hlive
      have ht := ih (allocate state offset node (users all active outputs offset)).state
        (offset+1) hs.2.2 hstep.1 hstep.2
      have hnext : state.next ≤ (allocate state offset node (users all active outputs offset)).state.next := by
        have he := allocate_count state offset node (users all active outputs offset) hlive
        have hp := List.length_pos_iff.mpr hlive
        change 0 < (users all active outputs offset).length at hp
        omega
      simp only [compileFrom, ha, ↓reduceIte]
      refine ⟨ht.1, ?_, hnext.trans ht.2.2.1, ?_⟩
      · convert ht.2.1 using 1; simp only [List.length_cons]; omega
      · intro gate hgate
        rcases List.mem_cons.mp hgate with rfl | hgate
        · exact allocate_layout state offset node _ hf hin
        · exact ht.2.2.2 gate hgate
    · have ht := ih state (offset+1) hs.2.2 hf (skip_domain _ state offset hd (hs.2.1 ha))
      simp only [compileFrom, ha, ↓reduceIte]
      refine ⟨ht.1, ?_, ht.2.2⟩
      convert ht.2.1 using 1; simp only [List.length_cons]; omega

/-- The executable scalar program emitted for a concrete allocated gate. -/
def Gate.program (gate : Gate) : Circuit.Program ℕ (ZMod 2) :=
  ReversibleFanout.gather (gate.inputs.headD 0) gate.inputs.tail ++
    ReversibleFanout.scatter (gate.inputs.headD 0) gate.outputs.tail

/-- Concatenate the actual allocation-order scalar instruction lists. -/
def Code.program (code : Code) : Circuit.Program ℕ (ZMod 2) :=
  code.gates.flatMap Gate.program

theorem Gate.program_eq_layout (gate : Gate) (layout : ReversibleFanout.Layout ℕ)
    (hi : layout.inputs = gate.inputs) (ho : layout.outputs = gate.outputs) :
    gate.program = layout.program := by
  unfold Gate.program
  rw [← hi, ← ho]
  rfl

theorem Gate.program_length (gate : Gate) (hg : gate.HasLayout) :
    gate.program.length = gate.inputs.length - 1 + (gate.outputs.length - 1) := by
  obtain ⟨layout, hi, ho⟩ := hg
  rw [gate.program_eq_layout layout hi ho, layout.program_length, hi, ho]

theorem Gate.program_involutions (gate : Gate) (hg : gate.HasLayout)
    (op : Circuit.Gate ℕ (ZMod 2)) (hop : op ∈ gate.program) : Function.Involutive op.run := by
  obtain ⟨layout, hi, ho⟩ := hg
  rw [gate.program_eq_layout layout hi ho] at hop
  obtain ⟨dst, src, hne, rfl⟩ := layout.program_add op hop
  exact ReversibleFanout.add_involutive dst src hne

/-- Reversing the concrete concatenated program restores arbitrary register
contents. This includes dirty unused slots and imposes no zero-input premise. -/
theorem Code.run_reverse (code : Code) (hg : ∀ gate ∈ code.gates, gate.HasLayout)
    (r : ℕ → ZMod 2) : Circuit.run code.program.reverse (Circuit.run code.program r) = r := by
  apply ReversibleFanout.run_reverse
  intro op hop
  obtain ⟨gate, hgate, hop⟩ := List.mem_flatMap.mp hop
  exact gate.program_involutions (hg gate hgate) op hop

theorem Code.reverse_run (code : Code) (hg : ∀ gate ∈ code.gates, gate.HasLayout)
    (r : ℕ → ZMod 2) : Circuit.run code.program (Circuit.run code.program.reverse r) = r := by
  have h := ReversibleFanout.run_reverse code.program.reverse (fun op hop => by
    obtain ⟨gate, hgate, hop⟩ := List.mem_flatMap.mp (List.mem_reverse.mp hop)
    exact gate.program_involutions (hg gate hgate) op hop) r
  simpa only [List.reverse_reverse] using h

/-- All actual input slots are inside the new role interval, including the
fresh pivot introduced for a source node. -/
theorem allocate_inputs_bounded {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) (hc : consumers ≠ []) (hf : Frontier state) (hi : InputsReady state index node) :
    ∀ r ∈ (allocate state index node consumers).gate.inputs,
      r < (allocate state index node consumers).state.next := by
  intro r hr
  have hp := List.length_pos_iff.mpr hc
  cases node with
  | mk kind support =>
    cases kind with
    | input label =>
      have he : r = state.next := by simpa [allocate] using hr
      change r < state.next+1+consumers.length-1
      omega
    | add left right =>
      have hl := hf.slot_lt _ hi.1
      have hright := hf.slot_lt _ hi.2
      have hm : r = slot state.live (.gate index false) ∨ r = slot state.live (.gate index true) := by
        simpa [allocate] using hr
      change r < state.next+consumers.length-1
      omega

def Gate.Bounded (roles : ℕ) (gate : Gate) : Prop :=
  ∀ r ∈ gate.inputs ++ gate.outputs, r < roles

/-- Every gate incidence in the actual execution is bounded by the final
allocated role count, so the emitted program is a finite-register program. -/
theorem compileFrom_gates_bounded {ι : Type*} (all : List (Node ι)) (active : Finset ℕ) (outputs : List ℕ)
    (state : State) (offset : ℕ) (nodes : List (Node ι))
    (hw : WiringValid (gatePortsFrom active 0 all ++ requestedPorts outputs))
    (hs : ScheduledFrom (gatePortsFrom active 0 all ++ requestedPorts outputs) active offset nodes)
    (hf : Frontier state) (hd : Domain (gatePortsFrom active 0 all ++ requestedPorts outputs) offset state) :
    let code := compileFrom all active outputs state offset nodes
    ∀ gate ∈ code.gates, gate.Bounded code.state.next := by
  induction nodes generalizing state offset with
  | nil => simp [compileFrom]
  | cons node nodes ih =>
    by_cases ha : offset ∈ active
    · obtain ⟨hearly, hlive⟩ := hs.1 ha
      have hin := inputsReady_domain _ state offset node hd hearly
      have hstep := allocate_frontier_domain _ offset state node hw hd hf hin hlive
      have ht := ih (allocate state offset node (users all active outputs offset)).state
        (offset+1) hs.2.2 hstep.1 hstep.2
      have hfut := compileFrom_frontier all active outputs
        (allocate state offset node (users all active outputs offset)).state (offset+1) nodes hw hs.2.2 hstep.1 hstep.2
      simp only [compileFrom, ha, ↓reduceIte]
      intro gate hgate
      rcases List.mem_cons.mp hgate with rfl | hgate
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact (allocate_inputs_bounded state offset node _ hlive hf hin r hr).trans_le hfut.2.2.1
        · exact (allocate_outputs_bounded state offset node _ hlive hf hin r hr).trans_le hfut.2.2.1
      · exact ht gate hgate
    · simpa only [compileFrom, ha, ↓reduceIte] using
        ih state (offset+1) hs.2.2 hf (skip_domain _ state offset hd (hs.2.1 ha))

/-- Every nonpivot input role actually disappears from the live frontier after
its value is gathered; it is neither retained nor assigned to a new consumer. -/
theorem allocate_retired_role {ι : Type*} (state : State) (index : ℕ) (node : Node ι)
    (consumers : List Port) (hf : Frontier state) (hi : InputsReady state index node)
    (r : ℕ) (hr : r ∈ (allocate state index node consumers).gate.inputs.tail) :
    r ∉ (allocate state index node consumers).state.live.map Prod.snd := by
  cases node with
  | mk kind support =>
    cases kind with
    | input label => simp [allocate] at hr
    | add left right =>
      have he : r = slot state.live (.gate index true) := by simpa [allocate] using hr
      subst r
      intro hm
      change slot state.live (.gate index true) ∈
        ((consumers.zip (allocate state index ⟨.add left right,support⟩ consumers).gate.outputs ++
          retained state index).map Prod.snd) at hm
      rw [List.map_append] at hm
      rcases List.mem_append.mp hm with hm | hm
      · obtain ⟨entry, he, hslot⟩ := List.mem_map.mp hm
        have hout := (List.of_mem_zip he).2
        rw [hslot] at hout
        have hp := (allocate_shared_pivot state index ⟨.add left right,support⟩ consumers hf hi
          (slot state.live (.gate index true))).mp ⟨by simp [allocate], hout⟩
        have hpq := hf.slot_ne (.gate index false) (.gate index true) hi.1 hi.2 (by simp)
        exact hpq hp.symm
      · obtain ⟨entry, he, hslot⟩ := List.mem_map.mp hm
        have howner := hf.slot_owner (.gate index true) hi.2 entry (List.mem_filter.mp he).1 hslot
        exact retired_absent state index true entry he howner

end IntegerMultBounds.Networks.DAGAllocator
