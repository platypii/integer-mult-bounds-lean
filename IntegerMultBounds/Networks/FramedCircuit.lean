import IntegerMultBounds.Networks.Circuit

/-! Compile a finite scalar circuit with a common linear frame at each gate.
The generated instructions explicitly change each touched wire from its current
frame to the next gate's frame, then execute the pointwise linear gate. Final
edge instructions apply the prescribed output frames to every enumerated wire,
including scratch and spectators. Frames are exact operators; no tape cost or
approximate implementation of a frame is assumed. -/

namespace IntegerMultBounds.Networks.FramedCircuit

open Circuit (Gate)

variable {ι R E : Type*} [DecidableEq ι] [CommRing R]
  [AddCommGroup E] [Module R E]

/-- The same finite scalar gate acting on vectors by scalar multiplication. -/
def moduleGate (g : Gate ι R) (x : ι → E) : ι → E :=
  Function.update x g.target (x g.target + (g.terms.map fun p => p.2 • x p.1).sum)

def moduleRun : List (Gate ι R) → (ι → E) → (ι → E)
  | [], x => x
  | g :: gs, x => moduleRun gs (moduleGate g x)

@[simp] theorem moduleRun_nil (x : ι → E) : moduleRun (R := R) [] x = x := rfl

@[simp] theorem moduleRun_cons (g : Gate ι R) (gs : List (Gate ι R)) (x : ι → E) :
    moduleRun (g :: gs) x = moduleRun gs (moduleGate g x) := rfl

/-- On arrays, the vector gate is exactly the existing scalar circuit gate at
each address, not a separate abstract notion of a network gate. -/
theorem moduleGate_pointwise {Ω : Type*} (g : Gate ι R) (x : ι → Ω → R)
    (i : ι) (ω : Ω) :
    moduleGate g x i ω = Circuit.Gate.run g (fun j => x j ω) i := by
  have hsum : ((g.terms.map fun p => p.2 • x p.1).sum) ω =
      (g.terms.map fun p => p.2 * x p.1 ω).sum := by
    generalize g.terms = ps
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [Pi.add_apply, Pi.smul_apply, ih, smul_eq_mul]
  by_cases hi : i = g.target
  · subst i
    simpa [moduleGate, Circuit.Gate.run, Pi.add_apply] using congrArg (x g.target ω + ·) hsum
  · simp [moduleGate, Circuit.Gate.run, Function.update_of_ne hi]

theorem moduleRun_pointwise {Ω : Type*} (p : List (Gate ι R)) (x : ι → Ω → R)
    (i : ι) (ω : Ω) :
    moduleRun p x i ω = Circuit.run p (fun j => x j ω) i := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [moduleRun_cons, ih, Circuit.run_cons]
    congr 1
    funext j
    exact moduleGate_pointwise g x j ω

/-- A read-only logical wire is preserved even when used by other gates. -/
theorem moduleRun_preserves (p : List (Gate ι R)) (x : ι → E) (i : ι)
    (h : ∀ g ∈ p, g.target ≠ i) : moduleRun p x i = x i := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [moduleRun_cons, ih _ (fun g hg => h g (by simp [hg]))]
    exact Function.update_of_ne (h g (by simp)).symm _ _

/-- Incidences include the target's old value as well as every listed source.
Repeated incidences are allowed; repeated alignment emits an identity change. -/
def touched (g : Gate ι R) : List ι := g.target :: g.terms.map Prod.fst

abbrev Frame (R E : Type*) [CommRing R] [AddCommGroup E] [Module R E] := E ≃ₗ[R] E

/-- Interpret a logical wire array in its currently recorded physical frame. -/
def encode (frames : ι → Frame R E) (x : ι → E) : ι → E := fun i => frames i (x i)

def decode (frames : ι → Frame R E) (x : ι → E) : ι → E := fun i => (frames i).symm (x i)

omit [DecidableEq ι] in
@[simp] theorem encode_decode (frames : ι → Frame R E) (x : ι → E) :
    encode frames (decode frames x) = x := by funext i; exact (frames i).apply_symm_apply _

omit [DecidableEq ι] in
@[simp] theorem decode_encode (frames : ι → Frame R E) (x : ι → E) :
    decode frames (encode frames x) = x := by funext i; exact (frames i).symm_apply_apply _

/-- An edge operator is applied to one wire, or a finite pointwise gate is run.
The instruction contains the actual old and new frames, not an unproved contract. -/
inductive Instruction (ι R E : Type*) [CommRing R] [AddCommGroup E] [Module R E] where
  | edge (wire : ι) (old next : Frame R E)
  | gate (g : Gate ι R)

def execute : Instruction ι R E → (ι → E) → (ι → E)
  | .edge i old next, x => Function.update x i (next (old.symm (x i)))
  | .gate g, x => moduleGate g x

def run : List (Instruction ι R E) → (ι → E) → (ι → E)
  | [], x => x
  | instr :: rest, x => run rest (execute instr x)

@[simp] theorem run_nil (x : ι → E) : run (R := R) [] x = x := rfl
@[simp] theorem run_cons (instr : Instruction ι R E) (rest : List (Instruction ι R E))
    (x : ι → E) : run (instr :: rest) x = run rest (execute instr x) := rfl

theorem run_append (p q : List (Instruction ι R E)) (x : ι → E) :
    run (p ++ q) x = run q (run p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons instr rest ih => exact ih _

/-- The frame profile after changing the specified wires in their listed order. -/
def afterEdges (current desired : ι → Frame R E) : List ι → ι → Frame R E
  | [] => current
  | i :: rest => afterEdges (Function.update current i (desired i)) desired rest

/-- Explicit edge instructions use the frame left by each preceding instruction. -/
def edges (current desired : ι → Frame R E) : List ι → List (Instruction ι R E)
  | [] => []
  | i :: rest => .edge i (current i) (desired i) ::
      edges (Function.update current i (desired i)) desired rest

theorem afterEdges_apply (current desired : ι → Frame R E) (wires : List ι) (i : ι) :
    afterEdges current desired wires i = if i ∈ wires then desired i else current i := by
  induction wires generalizing current with
  | nil => simp [afterEdges]
  | cons j rest ih =>
    rw [afterEdges, ih]
    by_cases hr : i ∈ rest <;> by_cases hij : i = j <;> simp [hr, hij]

/-- Every edge instruction preserves the per-wire stored/logical invariant. -/
theorem edge_invariant (current : ι → Frame R E) (next : Frame R E)
    (i : ι) (x : ι → E) :
    execute (.edge i (current i) next) (encode current x) =
      encode (Function.update current i next) x := by
  funext j
  by_cases hj : j = i
  · subst j; simp [execute, encode]
  · simp [execute, encode, Function.update_of_ne hj]

theorem edges_invariant (current desired : ι → Frame R E) (wires : List ι) (x : ι → E) :
    run (edges current desired wires) (encode current x) =
      encode (afterEdges current desired wires) x := by
  induction wires generalizing current with
  | nil => rfl
  | cons i rest ih => rw [edges, run_cons, edge_invariant, ih]; rfl

/-- The common-frame identity for the actual finite gate, including its target,
every source incidence, and all untouched wires. -/
theorem gate_invariant (g : Gate ι R) (current : ι → Frame R E) (D : Frame R E)
    (h : ∀ i ∈ touched g, current i = D) (x : ι → E) :
    moduleGate g (encode current x) = encode current (moduleGate g x) := by
  have ht : current g.target = D := h _ (by simp [touched])
  have hs : ∀ p ∈ g.terms, current p.1 = D := by
    intro p hp
    exact h _ (by simp only [touched, List.mem_cons, List.mem_map]; exact Or.inr ⟨p, hp, rfl⟩)
  have hsum : (g.terms.map fun p => p.2 • current p.1 (x p.1)).sum =
      D ((g.terms.map fun p => p.2 • x p.1).sum) := by
    rw [map_list_sum, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p hp
    simp [hs p hp]
  funext i
  by_cases hi : i = g.target
  · subst i
    simp only [moduleGate, Function.update_self, encode, ht, map_add]
    exact congrArg (D (x g.target) + ·) hsum
  · simp [moduleGate, encode, Function.update_of_ne hi]

/-- A gate together with its one common incidence frame. -/
structure FramedGate (ι R E : Type*) [CommRing R] [AddCommGroup E] [Module R E] where
  gate : Gate ι R
  frame : Frame R E

def afterGate (current : ι → Frame R E) (v : FramedGate ι R E) : ι → Frame R E :=
  afterEdges current (fun _ => v.frame) (touched v.gate)

def compileGate (current : ι → Frame R E) (v : FramedGate ι R E) :
    List (Instruction ι R E) :=
  edges current (fun _ => v.frame) (touched v.gate) ++ [.gate v.gate]

theorem compileGate_invariant (current : ι → Frame R E) (v : FramedGate ι R E)
    (x : ι → E) :
    run (compileGate current v) (encode current x) =
      encode (afterGate current v) (moduleGate v.gate x) := by
  rw [compileGate, run_append, edges_invariant]
  simp only [run_cons, run_nil, execute]
  apply gate_invariant v.gate _ v.frame
  intro i hi
  simp [afterEdges_apply, hi]

/-- The final per-wire frame profile after all gate incidences have been aligned. -/
def finalFrames (current : ι → Frame R E) : List (FramedGate ι R E) → ι → Frame R E
  | [] => current
  | v :: rest => finalFrames (afterGate current v) rest

/-- The generated finite instruction schedule, with all edge operators explicit. -/
def compile (current : ι → Frame R E) : List (FramedGate ι R E) → List (Instruction ι R E)
  | [] => []
  | v :: rest => compileGate current v ++ compile (afterGate current v) rest

theorem compile_invariant (current : ι → Frame R E) (vs : List (FramedGate ι R E))
    (x : ι → E) :
    run (compile current vs) (encode current x) =
      encode (finalFrames current vs) (moduleRun (vs.map FramedGate.gate) x) := by
  induction vs generalizing current x with
  | nil => rfl
  | cons v rest ih =>
    rw [compile, run_append, compileGate_invariant, ih]
    rfl

/-- Append the sink edges on every listed wire, including scratch/spectators. -/
def compileNetwork (wires : List ι) (input output : ι → Frame R E)
    (vs : List (FramedGate ι R E)) : List (Instruction ι R E) :=
  compile input vs ++ edges (finalFrames input vs) output wires

/-- All intermediate frames cancel. The supplied physical input is interpreted
through the inverse input frame; the generated schedule has no input preprocessing.
The output profile is applied on every wire, not just the data bank. -/
theorem common_frame_identity (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → Frame R E) (vs : List (FramedGate ι R E)) (stored : ι → E) :
    run (compileNetwork wires input output vs) stored =
      encode output (moduleRun (vs.map FramedGate.gate) (decode input stored)) := by
  have hframes : afterEdges (finalFrames input vs) output wires = output := by
    funext i
    simp [afterEdges_apply, hall i]
  conv_lhs => rw [← encode_decode input stored]
  rw [compileNetwork, run_append, compile_invariant, edges_invariant, hframes]

/-- The common-frame identity stated directly through the existing executable
scalar circuit at each address. Output frames may mix addresses arbitrarily. -/
theorem common_frame_array_identity {Ω : Type*} (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → Frame R (Ω → R)) (vs : List (FramedGate ι R (Ω → R)))
    (stored : ι → Ω → R) (i : ι) :
    run (compileNetwork wires input output vs) stored i =
      output i (fun ω => Circuit.run (vs.map FramedGate.gate)
        (fun j => (input j).symm (stored j) ω) i) := by
  rw [common_frame_identity wires hall]
  unfold encode
  congr 1
  funext ω
  exact moduleRun_pointwise _ _ i ω

/-- A logical spectator still receives its prescribed endpoint frame change;
its entire intermediate edge history cancels, even if gates read that wire. -/
theorem spectator_route (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → Frame R E) (vs : List (FramedGate ι R E))
    (stored : ι → E) (i : ι) (hs : ∀ v ∈ vs, v.gate.target ≠ i) :
    run (compileNetwork wires input output vs) stored i =
      output i ((input i).symm (stored i)) := by
  rw [common_frame_identity wires hall]
  change output i (moduleRun (vs.map FramedGate.gate) (decode input stored) i) = _
  rw [moduleRun_preserves _ _ i]
  · rfl
  · intro g hg
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hg
    exact hs v hv

/-- For fixed endpoint frames and scalar gates, arbitrary choices of common
intermediate frames give exactly the same complete network operator. -/
theorem independent_of_intermediate_frames (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → Frame R E) (vs ws : List (FramedGate ι R E))
    (hg : vs.map FramedGate.gate = ws.map FramedGate.gate) (stored : ι → E) :
    run (compileNetwork wires input output vs) stored =
      run (compileNetwork wires input output ws) stored := by
  rw [common_frame_identity wires hall, common_frame_identity wires hall, hg]

/-- Finite register banks have a concrete complete wire enumeration, including
zero registers, so the endpoint schedule needs no enumeration hypothesis. -/
def finiteNetwork {n : ℕ} (input output : Fin n → Frame R E)
    (vs : List (FramedGate (Fin n) R E)) : List (Instruction (Fin n) R E) :=
  compileNetwork (List.ofFn fun i : Fin n => i) input output vs

theorem finiteNetwork_identity {n : ℕ} (input output : Fin n → Frame R E)
    (vs : List (FramedGate (Fin n) R E)) (stored : Fin n → E) :
    run (finiteNetwork input output vs) stored =
      encode output (moduleRun (vs.map FramedGate.gate) (decode input stored)) := by
  apply common_frame_identity
  intro i
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

end IntegerMultBounds.Networks.FramedCircuit
