import IntegerMultBounds.Networks.DAGAllocatorRun
import IntegerMultBounds.Networks.DAGConsumers

/-! Unconditional structural correctness and exact role count of the actual
allocator on valid DAGs with in-bounds requested outputs. -/

namespace IntegerMultBounds.Networks.DAGAllocator

open DisjointCircuit

variable {ι : Type*} [DecidableEq ι]

/-- Every suffix of the real DAG scan satisfies the original-wiring schedule
conditions; no facts about allocator-produced slots are premises. -/
theorem marked_scheduled (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) :
    let active := DisjointPruning.mark nodes outputs.toFinset
    ScheduledFrom (gatePortsFrom active 0 nodes ++ requestedPorts outputs) active 0 nodes := by
  let active := DisjointPruning.mark nodes outputs.toFinset
  let wires := gatePortsFrom active 0 nodes ++ requestedPorts outputs
  have suffixes : ∀ (suffix before : List (Node ι)), nodes = before ++ suffix →
      ScheduledFrom wires active before.length suffix := by
    intro suffix
    induction suffix with
    | nil => intro before he; trivial
    | cons node suffix ih =>
      intro before he
      refine ⟨?_, ?_, ?_⟩
      · intro ha
        refine ⟨?_, users_mark_nonempty nodes outputs before.length ha⟩
        intro port hp
        have hi : before.length < nodes.length := by simp [he]
        have hnode : nodes[before.length] = node := by simp [he]
        apply active_input_earlier nodes active outputs hv before.length hi ha port
        rwa [hnode]
      · intro ha
        exact ⟨marked_inactive_no_owner nodes outputs hv ho before.length ha,
          inactive_no_target nodes active outputs before.length ha⟩
      · have hh := ih (before ++ [node]) (by simpa [List.append_assoc] using he)
        simpa only [List.length_append, List.length_singleton] using hh
  exact suffixes nodes [] (by simp)

/-- Actual compilation starts from an empty frontier, preserves its injectivity
and bounds, and emits only correctly shaped reversible fanout gates. -/
theorem compile_frontier (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) :
    let active := DisjointPruning.mark nodes outputs.toFinset
    let code := compile nodes outputs
    Frontier code.state ∧ Domain (gatePortsFrom active 0 nodes ++ requestedPorts outputs) nodes.length code.state ∧
      ∀ gate ∈ code.gates, gate.HasLayout := by
  let active := DisjointPruning.mark nodes outputs.toFinset
  have hf : Frontier ⟨0,[]⟩ := ⟨by simp, by simp, by simp⟩
  have hd : Domain (gatePortsFrom active 0 nodes ++ requestedPorts outputs) 0 ⟨0,[]⟩ := by
    intro port
    simp
  have hh := compileFrom_frontier nodes active outputs ⟨0,[]⟩ 0 nodes (wiring_valid nodes active outputs hv)
    (marked_scheduled nodes outputs hv ho) hf hd
  exact ⟨hh.1, by simpa [compile, active] using hh.2.1, hh.2.2.2⟩

/-- Each actual emitted gate has distinct inputs and outputs and shares only
its first input pivot, proved from the original DAG validity. -/
theorem compile_gate_layout (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (gate : Gate) (hg : gate ∈ (compile nodes outputs).gates) :
    gate.inputs.Nodup ∧ gate.outputs.Nodup ∧
      ∀ slot, slot ∈ gate.inputs ∧ slot ∈ gate.outputs ↔ slot = gate.inputs.headD 0 := by
  obtain ⟨layout, hi, hout⟩ := (compile_frontier nodes outputs hv ho).2.2 gate hg
  rw [← hi, ← hout]
  exact ⟨layout.inputs_nodup, layout.outputs_nodup, fun slot => by simpa [ReversibleFanout.Layout.inputs] using layout.shared_only_pivot slot⟩

/-- The complete actual allocated scalar program has an executable inverse
on arbitrary register contents, including dirty scratch roles. -/
theorem compile_run_reverse (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (r : ℕ → ZMod 2) :
    Circuit.run (compile nodes outputs).program.reverse (Circuit.run (compile nodes outputs).program r) = r :=
  (compile nodes outputs).run_reverse (compile_frontier nodes outputs hv ho).2.2 r

theorem compile_reverse_run (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (r : ℕ → ZMod 2) :
    Circuit.run (compile nodes outputs).program (Circuit.run (compile nodes outputs).program.reverse r) = r :=
  (compile nodes outputs).reverse_run (compile_frontier nodes outputs hv ho).2.2 r

/-- The final association lookup used for a requested output index. -/
def Code.outputSlot (code : Code) (index : ℕ) : ℕ := slot code.state.live (.output index)

omit [DecidableEq ι] in
theorem requestedPort_mem (outputs : List ℕ) (index : ℕ) (hi : index < outputs.length) :
    (outputs[index], .output index) ∈ requestedPorts outputs := by
  have hiz : index < (outputs.zipIdx).length := by simpa only [List.length_zipIdx] using hi
  have hm := List.getElem_mem hiz
  simp only [List.getElem_zipIdx, Nat.zero_add] at hm
  exact List.mem_map.mpr ⟨(outputs[index],index), hm, rfl⟩

omit [DecidableEq ι] in
theorem requestedPort_bound (outputs : List ℕ) (owner index : ℕ)
    (hp : (owner,.output index) ∈ requestedPorts outputs) : index < outputs.length := by
  obtain ⟨⟨value,i⟩, hm, he⟩ := List.mem_map.mp hp
  have he' : i = index := Port.output.inj (congrArg Prod.snd he)
  have hh := (List.mem_zipIdx hm).2.1
  omega

/-- Every requested output gets a real final frontier entry, even if several
requested outputs refer to the same DAG node. -/
theorem compile_output_present (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (index : ℕ) (hi : index < outputs.length) :
    .output index ∈ (compile nodes outputs).state.live.map Prod.fst := by
  apply (compile_frontier nodes outputs hv ho).2.1 (.output index) |>.mpr
  exact ⟨⟨outputs[index], ho _ (List.getElem_mem hi),
    List.mem_append_right _ (requestedPort_mem outputs index hi)⟩, trivial⟩

/-- The executable output lookup always returns an allocated role. -/
theorem compile_output_bound (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (index : ℕ) (hi : index < outputs.length) :
    (compile nodes outputs).outputSlot index < (compile nodes outputs).state.next :=
  (compile_frontier nodes outputs hv ho).1.slot_lt _ (compile_output_present nodes outputs hv ho index hi)

/-- Different requested output ports are physically distinct roles, including
repeated requests for an identical DAG output value. -/
theorem compile_output_ne (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (i j : ℕ) (hi : i < outputs.length)
    (hj : j < outputs.length) (hne : i ≠ j) :
    (compile nodes outputs).outputSlot i ≠ (compile nodes outputs).outputSlot j :=
  (compile_frontier nodes outputs hv ho).1.slot_ne _ _
    (compile_output_present nodes outputs hv ho i hi) (compile_output_present nodes outputs hv ho j hj)
    (fun h => hne (Port.output.inj h))

/-- No gate input ports survive the scan: the final live frontier consists
precisely of requested output ports; all other roles have retired. -/
theorem compile_live_output (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) (entry : Port × ℕ)
    (he : entry ∈ (compile nodes outputs).state.live) :
    ∃ index, index < outputs.length ∧ entry.1 = .output index := by
  have hd := (compile_frontier nodes outputs hv ho).2.1 entry.1 |>.mp (List.mem_map.mpr ⟨entry,he,rfl⟩)
  obtain ⟨⟨owner, howner, hw⟩, hp⟩ := hd
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨target, right, htarget, _, _, hbound⟩ := gatePorts_target _ 0 nodes (owner,entry.1) hw
    change entry.1 = .gate target right at htarget
    rw [htarget] at hp
    change nodes.length ≤ target at hp
    omega
  · obtain ⟨index, hindex⟩ := requestedPorts_output outputs (owner,entry.1) hw
    change entry.1 = .output index at hindex
    refine ⟨index, ?_, hindex⟩
    apply requestedPort_bound outputs owner index
    rwa [hindex] at hw

/-- Every intermediate gate uses only roles below the final actual allocation
count, including retired nonpivot inputs and fresh intermediate outputs. -/
theorem compile_gates_bounded (nodes : List (Node ι)) (outputs : List ℕ) (hv : Valid nodes)
    (ho : ∀ i ∈ outputs, i < nodes.length) :
    ∀ gate ∈ (compile nodes outputs).gates, gate.Bounded (compile nodes outputs).state.next := by
  let active := DisjointPruning.mark nodes outputs.toFinset
  have hf : Frontier ⟨0,[]⟩ := ⟨by simp, by simp, by simp⟩
  have hd : Domain (gatePortsFrom active 0 nodes ++ requestedPorts outputs) 0 ⟨0,[]⟩ := by
    intro port
    simp
  exact compileFrom_gates_bounded nodes active outputs ⟨0,[]⟩ 0 nodes
    (wiring_valid nodes active outputs hv) (marked_scheduled nodes outputs hv ho) hf hd

end IntegerMultBounds.Networks.DAGAllocator
