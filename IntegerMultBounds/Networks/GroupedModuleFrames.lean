import IntegerMultBounds.Networks.GroupedFrames

/-! The actual grouped common-frame compiler over an arbitrary module. Scalar
coefficients and the exact physical incidence/label trace are unchanged when
the stored values live in another module, including complex-valued arrays
viewed as a rational module. -/

namespace IntegerMultBounds.Networks.GroupedModuleFrames

open GroupedCircuit GroupedFrames
variable {ι L R E : Type*} [DecidableEq ι] [CommRing R]
  [AddCommGroup E] [Module R E]

theorem moduleRun_append (p q : Circuit.Program ι R) (x : ι → E) :
    FramedCircuit.moduleRun (p ++ q) x =
      FramedCircuit.moduleRun q (FramedCircuit.moduleRun p x) := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih => exact ih _

section Compiler
variable [DecidableEq R] (frameOf : L → FramedCircuit.Frame R E)

def profile (current : ι → L) : ι → FramedCircuit.Frame R E := fun i => frameOf (current i)

theorem after_profile (current : ι → L) (v : Vertex ι L R) :
    FramedCircuit.afterEdges (profile frameOf current) (fun _ => frameOf v.label) (touched v.group) =
      profile frameOf (after current v) := by
  funext i
  rw [FramedCircuit.afterEdges_apply]
  change (if i ∈ touched v.group then frameOf v.label else frameOf (current i)) =
    frameOf (RankTrace.finish current ((touched v.group).map fun j => (j, v.label)) i)
  rw [RankTrace.finish_align]
  split_ifs <;> rfl

/-- Compile the same labeled groups, now permitting any module-valued wires. -/
def compile (current : ι → L) : List (Vertex ι L R) → List (FramedCircuit.Instruction ι R E)
  | [] => []
  | v :: rest => compileFramed v.group (profile frameOf current) (frameOf v.label) ++
      compile (after current v) rest

/-- The grouped frame invariant holds for the actual scalar programs acting
by scalar multiplication on the module. -/
theorem compile_invariant (current : ι → L) (vs : List (Vertex ι L R)) (x : ι → E) :
    FramedCircuit.run (compile frameOf current vs) (FramedCircuit.encode (profile frameOf current) x) =
      FramedCircuit.encode (profile frameOf (finalLabels current vs))
        (FramedCircuit.moduleRun (compileGroups (vs.map Vertex.group)) x) := by
  induction vs generalizing current x with
  | nil => rfl
  | cons v rest ih =>
    rw [compile, FramedCircuit.run_append, compileFramed_invariant, after_profile, ih]
    simp only [List.map_cons, compileGroups, List.flatMap_cons, moduleRun_append, finalLabels]

/-- Append precisely the old compiler's sink incidence list. -/
def network (wires : List ι) (input output : ι → L) (vs : List (Vertex ι L R)) :
    List (FramedCircuit.Instruction ι R E) :=
  compile frameOf input vs ++ FramedCircuit.edges (profile frameOf (finalLabels input vs))
    (profile frameOf output) wires

/-- All intermediate module frames cancel along the complete physical
network, including scratch and spectator wires. -/
theorem network_identity (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → L) (vs : List (Vertex ι L R)) (stored : ι → E) :
    FramedCircuit.run (network frameOf wires input output vs) stored =
      FramedCircuit.encode (profile frameOf output)
        (FramedCircuit.moduleRun (compileGroups (vs.map Vertex.group))
          (FramedCircuit.decode (profile frameOf input) stored)) := by
  have hfinal : FramedCircuit.afterEdges (profile frameOf (finalLabels input vs))
      (profile frameOf output) wires = profile frameOf output := by
    funext i
    simp [FramedCircuit.afterEdges_apply, hall i]
  conv_lhs => rw [← FramedCircuit.encode_decode (profile frameOf input) stored]
  rw [network, FramedCircuit.run_append, compile_invariant, FramedCircuit.edges_invariant, hfinal]

/-- The label history is literally the existing global rank-accounting trace;
it is independent of the module that holds the wire values. -/
abbrev networkUpdates := GroupedFrames.networkUpdates (ι := ι) (L := L) (R := R)

theorem network_trace_final (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → L) (vs : List (Vertex ι L R)) :
    RankTrace.finish input (networkUpdates wires output vs) = output :=
  GroupedFrames.network_trace_final wires hall input output vs

/-- Extract ordered old/new frame pairs from the literal instruction list. -/
def edgePairs : List (FramedCircuit.Instruction ι R E) →
    List (FramedCircuit.Frame R E × FramedCircuit.Frame R E)
  | [] => []
  | .edge _ old next :: rest => (old, next) :: edgePairs rest
  | .gate _ :: rest => edgePairs rest

omit [DecidableEq ι] [DecidableEq R] in
@[simp] theorem edgePairs_append (p q : List (FramedCircuit.Instruction ι R E)) :
    edgePairs (p ++ q) = edgePairs p ++ edgePairs q := by
  induction p with
  | nil => rfl
  | cons instr p ih => cases instr <;> simp [edgePairs, ih]

omit [DecidableEq ι] [DecidableEq R] in
@[simp] theorem edgePairs_gates (rows : Circuit.Program ι R) :
    edgePairs (E := E) (rows.map FramedCircuit.Instruction.gate) = [] := by
  induction rows with
  | nil => rfl
  | cons g gs ih => exact ih

omit [DecidableEq R] in
/-- The profile update is exactly the same physical wire-label update. -/
theorem profile_update (current : ι → L) (i : ι) (next : L) :
    Function.update (profile frameOf current) i (frameOf next) =
      profile frameOf (Function.update current i next) := by
  funext j
  by_cases hj : j = i <;> simp [profile, hj]

omit [DecidableEq R] in
/-- Every alignment instruction contributes its actual consecutive labels,
including repeated incidences and the identity changes they generate. -/
theorem edgePairs_edges (current desired : ι → L) (wires : List ι) :
    edgePairs (FramedCircuit.edges (profile frameOf current) (profile frameOf desired) wires) =
      (RankTrace.edges current (wires.map fun i => (i, desired i))).map
        (fun p => (frameOf p.1, frameOf p.2)) := by
  induction wires generalizing current with
  | nil => rfl
  | cons i wires ih =>
    simp only [FramedCircuit.edges, edgePairs, List.map_cons, RankTrace.edges]
    change (frameOf (current i), frameOf (desired i)) :: _ = _
    rw [show profile frameOf desired i = frameOf (desired i) from rfl, profile_update, ih]

/-- Grouped compilation's ordered frame edges coincide with the existing
rank-accounting edge list, without adding edges for internal gate rows. -/
theorem edgePairs_compile (current : ι → L) (vs : List (Vertex ι L R)) :
    edgePairs (compile frameOf current vs) =
      (RankTrace.edges current (updates vs)).map (fun p => (frameOf p.1, frameOf p.2)) := by
  induction vs generalizing current with
  | nil => rfl
  | cons v vs ih =>
    rw [compile, edgePairs_append, GroupedCircuit.compileFramed, edgePairs_append, edgePairs_gates,
      List.append_nil, ih]
    have he : edgePairs (FramedCircuit.edges (profile frameOf current)
        (fun _ => frameOf v.label) (touched v.group)) =
        (RankTrace.edges current (touches v)).map (fun p => (frameOf p.1, frameOf p.2)) :=
      edgePairs_edges frameOf current (fun _ => v.label) (touched v.group)
    rw [he]
    simp only [updates, List.flatMap_cons, RankTrace.edges_append, List.map_append, after]

/-- Exact ordered correspondence between the module compiler's physical
frame instructions and the complete global trace used by rank factors. -/
theorem edgePairs_network (wires : List ι) (input output : ι → L) (vs : List (Vertex ι L R)) :
    edgePairs (network frameOf wires input output vs) =
      (RankTrace.edges input (networkUpdates wires output vs)).map
        (fun p => (frameOf p.1, frameOf p.2)) := by
  rw [network, edgePairs_append, edgePairs_compile, edgePairs_edges]
  simp only [networkUpdates, GroupedFrames.networkUpdates, RankTrace.edges_append,
    List.map_append, finalLabels_trace]

end Compiler

section Transfer

/-- Each scalar gate is a linear operator on any module-valued wire bank. -/
def gateLinear (g : Circuit.Gate ι R) : (ι → E) →ₗ[R] (ι → E) :=
  LinearMap.id + (LinearMap.single R (fun _ : ι => E) g.target).comp
    ((g.terms.map fun p => p.2 • (LinearMap.proj p.1 : (ι → E) →ₗ[R] E)).sum)

theorem gateLinear_apply (g : Circuit.Gate ι R) (x : ι → E) :
    gateLinear g x = FramedCircuit.moduleGate g x := by
  have hsum : ((g.terms.map fun p => p.2 • (LinearMap.proj p.1 : (ι → E) →ₗ[R] E)).sum) x =
      (g.terms.map fun p => p.2 • x p.1).sum := by
    induction g.terms with
    | nil => simp
    | cons p ps ih => simp [ih]
  funext i
  by_cases hi : i = g.target
  · subst i
    simp [gateLinear, FramedCircuit.moduleGate, hsum]
  · simp [gateLinear, FramedCircuit.moduleGate, hsum, hi]

/-- The actual compiled elementary program as a module-linear operator. -/
def runLinear : Circuit.Program ι R → ((ι → E) →ₗ[R] (ι → E))
  | [] => LinearMap.id
  | g :: gs => (runLinear gs).comp (gateLinear g)

theorem runLinear_apply (p : Circuit.Program ι R) (x : ι → E) :
    runLinear p x = FramedCircuit.moduleRun p x := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih => simp only [runLinear, LinearMap.comp_apply, gateLinear_apply, ih, FramedCircuit.moduleRun_cons]

variable {F : Type*} [AddCommGroup F] [Module R F]

/-- Module-valued execution commutes with every linear change of value module. -/
theorem moduleGate_map (f : E →ₗ[R] F) (g : Circuit.Gate ι R) (x : ι → E) :
    FramedCircuit.moduleGate g (fun i => f (x i)) = fun i => f (FramedCircuit.moduleGate g x i) := by
  funext i
  by_cases hi : i = g.target
  · subst i
    simp [FramedCircuit.moduleGate, map_list_sum, List.map_map, Function.comp_def]
  · simp [FramedCircuit.moduleGate, hi]

theorem moduleRun_map (f : E →ₗ[R] F) (p : Circuit.Program ι R) (x : ι → E) :
    FramedCircuit.moduleRun p (fun i => f (x i)) = fun i => f (FramedCircuit.moduleRun p x i) := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih => rw [FramedCircuit.moduleRun_cons, moduleGate_map, ih]; rfl

/-- Scalar module execution is exactly the original executable circuit. -/
theorem moduleRun_scalar (p : Circuit.Program ι R) (x : ι → R) :
    FramedCircuit.moduleRun p x = Circuit.run p x := by
  induction p generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [FramedCircuit.moduleRun_cons, ih, Circuit.run_cons]
    rfl

variable [Fintype ι]

/-- Every output value is the same finite scalar coefficient row applied to
module-valued inputs. No freeness or basis assumption is made on the module. -/
theorem moduleRun_coefficients (p : Circuit.Program ι R) (x : ι → E) (i : ι) :
    FramedCircuit.moduleRun p x i = ∑ j, Circuit.run p (Pi.single j 1) i • x j := by
  have hsingle (j : ι) : FramedCircuit.moduleRun p (Pi.single j (x j)) =
      fun i => Circuit.run p (Pi.single j 1) i • x j := by
    have h := moduleRun_map (LinearMap.toSpanSingleton R E (x j)) p (Pi.single j 1)
    rw [moduleRun_scalar] at h
    have he : (fun i => (LinearMap.toSpanSingleton R E (x j)) ((Pi.single j (1 : R) : ι → R) i)) = Pi.single j (x j) := by
      funext i
      by_cases hi : i = j <;> simp [hi]
    rw [he] at h
    exact h
  rw [← runLinear_apply]
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [runLinear_apply, hsingle]

/-- Equality on all scalar inputs transfers to every module-valued input,
while retaining the literal same finite programs and scalar coefficients. -/
theorem moduleRun_eq_of_scalar_eq (p q : Circuit.Program ι R)
    (h : ∀ x : ι → R, Circuit.run p x = Circuit.run q x) (x : ι → E) :
    FramedCircuit.moduleRun p x = FramedCircuit.moduleRun q x := by
  funext i
  simp only [moduleRun_coefficients, h]

/-- A scalar routing identity transfers directly to arbitrary module values. -/
theorem moduleRun_route (p : Circuit.Program ι R) (route : ι → ι)
    (h : ∀ x : ι → R, Circuit.run p x = fun i => x (route i)) (x : ι → E) :
    FramedCircuit.moduleRun p x = fun i => x (route i) := by
  funext i
  rw [moduleRun_coefficients]
  simp [h, Pi.single_apply]

/-- Signed scalar bank routes lift without altering coefficients or the
compiled wire schedule. This includes the rational signed exchange. -/
theorem moduleRun_signed_route (p : Circuit.Program ι R) (route : ι → ι) (sign : ι → R)
    (h : ∀ x : ι → R, Circuit.run p x = fun i => sign i * x (route i)) (x : ι → E) :
    FramedCircuit.moduleRun p x = fun i => sign i • x (route i) := by
  funext i
  rw [moduleRun_coefficients]
  simp [h, Pi.single_apply, mul_ite]

end Transfer
section RoutedNetwork
variable [Fintype ι] [DecidableEq R] (frameOf : L → FramedCircuit.Frame R E)

/-- A proved scalar signed routing identity yields the full common-frame
network identity on every module-valued wire, with the same grouped gates. -/
theorem network_signed_route (wires : List ι) (hall : ∀ i, i ∈ wires)
    (input output : ι → L) (vs : List (Vertex ι L R)) (route : ι → ι) (sign : ι → R)
    (h : ∀ x : ι → R, runGroups (vs.map Vertex.group) x = fun i => sign i * x (route i))
    (stored : ι → E) :
    FramedCircuit.run (network frameOf wires input output vs) stored =
      fun i => frameOf (output i) (sign i • (frameOf (input (route i))).symm (stored (route i))) := by
  rw [network_identity frameOf wires hall,
    moduleRun_signed_route _ route sign (fun x => by rw [compileGroups_run]; exact h x)]
  rfl

end RoutedNetwork

end IntegerMultBounds.Networks.GroupedModuleFrames
