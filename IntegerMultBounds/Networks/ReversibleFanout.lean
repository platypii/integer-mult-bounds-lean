import IntegerMultBounds.Networks.CircuitBits

/-! The literal reversible fanout gate used by the pair-exclusion compiler.
A pivot accumulates its other inputs, then copies that sum into fresh output
slots. Elementary steps and their reversed inverse are actual scalar programs. -/

namespace IntegerMultBounds.Networks.ReversibleFanout

open Circuit
variable {ι : Type*} [DecidableEq ι]

/-- A single XOR update, with its source explicitly represented in the program. -/
def add (dst src : ι) : Circuit.Gate ι (ZMod 2) := ⟨dst, [(src, 1)]⟩

@[simp] theorem add_run (dst src : ι) (r : ι → ZMod 2) :
    (add dst src).run r = Function.update r dst (r dst + r src) := by
  simp [add, Circuit.Gate.run]

/-- A non-self XOR update is its own inverse on arbitrary contents. -/
theorem add_involutive (dst src : ι) (hne : dst ≠ src) : Function.Involutive (add dst src).run := by
  intro r
  funext k
  by_cases hk : k = dst
  · subst k
    simp only [add_run, Function.update_self, Function.update_of_ne (Ne.symm hne)]
    have hz : r src + r src = 0 := by
      simpa only [ZMod.neg_eq_self_mod_two] using add_neg_cancel (r src)
    rw [add_assoc, hz, add_zero]
  · simp [add_run, Function.update_of_ne hk]

/-- Nonpivot input slots are read and retired; only the pivot is overwritten. -/
def gather (pivot : ι) (inputs : List ι) : Circuit.Program ι (ZMod 2) :=
  inputs.map (add pivot)

/-- New nonpivot output slots each receive one XOR from the completed pivot. -/
def scatter (pivot : ι) (outputs : List ι) : Circuit.Program ι (ZMod 2) :=
  outputs.map (fun dst => add dst pivot)

/-- The actual layout has distinct input and output lists, intersecting only
at their shared first pivot. The stored lists omit that first pivot. -/
structure Layout (ι : Type*) where
  pivot : ι
  inputTail : List ι
  outputTail : List ι
  input_nodup : inputTail.Nodup
  output_nodup : outputTail.Nodup
  pivot_not_input : pivot ∉ inputTail
  pivot_not_output : pivot ∉ outputTail
  tails_disjoint : inputTail.Disjoint outputTail

namespace Layout

def inputs (g : Layout ι) : List ι := g.pivot :: g.inputTail
def outputs (g : Layout ι) : List ι := g.pivot :: g.outputTail

def program (g : Layout ι) : Circuit.Program ι (ZMod 2) :=
  gather g.pivot g.inputTail ++ scatter g.pivot g.outputTail

def inverse (g : Layout ι) : Circuit.Program ι (ZMod 2) := g.program.reverse

omit [DecidableEq ι] in
@[simp] theorem inputs_nodup (g : Layout ι) : g.inputs.Nodup :=
  List.nodup_cons.mpr ⟨g.pivot_not_input, g.input_nodup⟩

omit [DecidableEq ι] in
@[simp] theorem outputs_nodup (g : Layout ι) : g.outputs.Nodup :=
  List.nodup_cons.mpr ⟨g.pivot_not_output, g.output_nodup⟩

omit [DecidableEq ι] in
theorem shared_only_pivot (g : Layout ι) (i : ι) :
    i ∈ g.inputs ∧ i ∈ g.outputs ↔ i = g.pivot := by
  simp only [inputs, outputs, List.mem_cons]
  constructor
  · rintro ⟨hi | hi, ho | ho⟩
    · exact hi
    · exact hi
    · exact ho
    · exact (g.tails_disjoint hi ho).elim
  · intro hi
    exact ⟨Or.inl hi, Or.inl hi⟩

omit [DecidableEq ι] in
/-- One instruction per nonpivot input and per nonpivot output. -/
theorem program_length (g : Layout ι) :
    g.program.length = g.inputs.length - 1 + (g.outputs.length - 1) := by
  simp [program, gather, scatter, inputs, outputs]
end Layout

/-- Gathering has an exact whole-register-file specification. -/
theorem gather_run (pivot : ι) (inputs : List ι) (hp : pivot ∉ inputs) (r : ι → ZMod 2) :
    Circuit.run (gather pivot inputs) r =
      Function.update r pivot (r pivot + (inputs.map r).sum) := by
  induction inputs generalizing r with
  | nil => simp [gather, Function.update_eq_self]
  | cons src rest ih =>
    have hsp : src ≠ pivot := by intro he; subst src; exact hp (by simp)
    have hrest : pivot ∉ rest := fun hh => hp (by simp [hh])
    have hm : rest.map (Function.update r pivot (r pivot + r src)) = rest.map r := by
      apply List.map_congr_left
      intro i hi
      exact Function.update_of_ne (by intro he; subst i; exact hrest hi) _ _
    simp only [gather, List.map_cons, Circuit.run_cons] at *
    rw [ih hrest, add_run]
    simp only [Function.update_self, hm, Function.update_idem, List.sum_cons]
    rw [add_assoc]

/-- Scattering updates each distinct output exactly once and leaves the pivot
and all other registers unchanged. -/
theorem scatter_run (pivot : ι) (outputs : List ι) (hn : outputs.Nodup)
    (hp : pivot ∉ outputs) (r : ι → ZMod 2) (k : ι) :
    Circuit.run (scatter pivot outputs) r k =
      if k ∈ outputs then r k + r pivot else r k := by
  induction outputs generalizing r with
  | nil => simp [scatter]
  | cons dst rest ih =>
    obtain ⟨hdrest, hrest⟩ := List.nodup_cons.mp hn
    have hpRest : pivot ∉ rest := fun hh => hp (by simp [hh])
    have hpd : pivot ≠ dst := by intro he; subst dst; exact hp (by simp)
    simp only [scatter, List.map_cons, Circuit.run_cons] at *
    rw [ih hrest hpRest, add_run]
    by_cases hkd : k = dst
    · subst k
      simp [hdrest]
    · simp [hkd, Function.update_of_ne hpd]

namespace Layout

/-- The sum represented by a node's explicit input slots, before execution. -/
def inputSum (g : Layout ι) (r : ι → ZMod 2) : ZMod 2 := (g.inputs.map r).sum

/-- Exact semantics on arbitrary contents, including dirty output slots. -/
theorem run_apply (g : Layout ι) (r : ι → ZMod 2) (k : ι) :
    Circuit.run g.program r k =
      if k = g.pivot then g.inputSum r
      else if k ∈ g.outputTail then r k + g.inputSum r else r k := by
  rw [program, Circuit.run_append, scatter_run _ _ g.output_nodup g.pivot_not_output,
    gather_run _ _ g.pivot_not_input]
  by_cases hk : k = g.pivot
  · subst k
    simp [g.pivot_not_output, inputSum, inputs]
  · simp [hk, inputSum, inputs]

/-- With the fresh nonpivot outputs zeroed, every declared output contains the
same exact sum of all declared inputs. -/
theorem fresh_outputs (g : Layout ι) (r : ι → ZMod 2)
    (hfresh : ∀ i ∈ g.outputTail, r i = 0) (k : ι) (hk : k ∈ g.outputs) :
    Circuit.run g.program r k = g.inputSum r := by
  rw [run_apply]
  rcases List.mem_cons.mp hk with rfl | hk
  · simp
  · simp [hfresh k hk, hk]

/-- Every nonpivot input is preserved even though its value is accumulated. -/
theorem input_preserved (g : Layout ι) (r : ι → ZMod 2) (k : ι) (hk : k ∈ g.inputTail) :
    Circuit.run g.program r k = r k := by
  have hkp : k ≠ g.pivot := by intro he; subst k; exact g.pivot_not_input hk
  have hko : k ∉ g.outputTail := fun ho => g.tails_disjoint hk ho
  simp [run_apply, hkp, hko]

/-- Registers outside the declared input/output incidence are untouched. -/
theorem outside_preserved (g : Layout ι) (r : ι → ZMod 2) (k : ι)
    (hin : k ∉ g.inputs) (hout : k ∉ g.outputs) : Circuit.run g.program r k = r k := by
  have hkp : k ≠ g.pivot := fun he => hin (List.mem_cons.mpr (Or.inl he))
  have hko : k ∉ g.outputTail := fun hk => hout (List.mem_cons.mpr (Or.inr hk))
  simp [run_apply, hkp, hko]

omit [DecidableEq ι] in
/-- Every literal elementary operation has different source and destination. -/
theorem program_add (g : Layout ι) (op : Circuit.Gate ι (ZMod 2)) (hop : op ∈ g.program) :
    ∃ dst src, dst ≠ src ∧ op = add dst src := by
  simp only [program, gather, scatter, List.mem_append, List.mem_map] at hop
  rcases hop with ⟨src, hs, rfl⟩ | ⟨dst, hd, rfl⟩
  · exact ⟨g.pivot, src, by intro he; subst src; exact g.pivot_not_input hs, rfl⟩
  · exact ⟨dst, g.pivot, by intro he; subst dst; exact g.pivot_not_output hd, rfl⟩
end Layout

/-- Reversing a list of self-inverse instructions is its actual executable inverse. -/
theorem run_reverse (p : Circuit.Program ι (ZMod 2))
    (hp : ∀ op ∈ p, Function.Involutive op.run) (r : ι → ZMod 2) :
    Circuit.run p.reverse (Circuit.run p r) = r := by
  induction p generalizing r with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.reverse_cons, Circuit.run_append, Circuit.run_cons, Circuit.run_nil]
    rw [ih (fun q hq => hp q (by simp [hq])), hp op (by simp)]

/-- Registers actually read or written by nonzero scalar instructions. -/
def instructionSupport (p : Circuit.Program ι (ZMod 2)) : Finset ι :=
  (p.flatMap fun op => op.target ::
    ((op.terms.filter fun term => term.2 ≠ 0).map Prod.fst)).toFinset

namespace Layout

/-- Logical group incidences include the shared pivot even for an identity
node with no elementary instructions. -/
def incidence (g : Layout ι) : Finset ι := (g.inputs ++ g.outputs).toFinset

@[simp] theorem mem_incidence (g : Layout ι) (k : ι) :
    k ∈ g.incidence ↔ k = g.pivot ∨ k ∈ g.inputTail ∨ k ∈ g.outputTail := by
  simp only [incidence, inputs, outputs, List.mem_toFinset, List.mem_append, List.mem_cons]
  tauto

/-- Exact support of the elementary gather/scatter lists, retaining whether
there is any instruction which actually reads or writes the pivot. -/
theorem mem_instructionSupport (g : Layout ι) (k : ι) :
    k ∈ instructionSupport g.program ↔
      (∃ i ∈ g.inputTail, k = g.pivot ∨ k = i) ∨
      (∃ i ∈ g.outputTail, k = i ∨ k = g.pivot) := by
  simp [instructionSupport, program, gather, scatter, add]

theorem instructionSupport_subset (g : Layout ι) : instructionSupport g.program ⊆ g.incidence := by
  intro k hk
  rw [mem_instructionSupport] at hk
  rw [mem_incidence]
  rcases hk with ⟨i, hi, hp | rfl⟩ | ⟨i, hi, rfl | hp⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)
  · exact Or.inl hp

/-- Every nonidentity gate touches exactly its input/output union. -/
theorem instructionSupport_eq (g : Layout ι)
    (hactive : g.inputTail ≠ [] ∨ g.outputTail ≠ []) :
    instructionSupport g.program = g.incidence := by
  apply Finset.Subset.antisymm (instructionSupport_subset g)
  intro k hk
  rw [mem_incidence] at hk
  rw [mem_instructionSupport]
  rcases hk with rfl | hk | hk
  · rcases hactive with hi | ho
    · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hi
      exact Or.inl ⟨i, hi, Or.inl rfl⟩
    · obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ ho
      exact Or.inr ⟨i, hi, Or.inr rfl⟩
  · exact Or.inl ⟨k, hk, Or.inr rfl⟩
  · exact Or.inr ⟨k, hk, Or.inl rfl⟩

/-- The only exceptional layout is the declared one-wire identity node. -/
theorem identity_support (g : Layout ι) (hi : g.inputTail = []) (ho : g.outputTail = []) :
    g.program = [] ∧ instructionSupport g.program = ∅ ∧ g.incidence = {g.pivot} := by
  simp [program, gather, scatter, hi, ho, instructionSupport, incidence, inputs, outputs]

/-- Zero-cost identity nodes still declare their pivot incidence for framing. -/
theorem incidence_eq_support_insert (g : Layout ι) :
    g.incidence = insert g.pivot (instructionSupport g.program) := by
  by_cases hi : g.inputTail = []
  · by_cases ho : g.outputTail = []
    · rw [(identity_support g hi ho).2.1, (identity_support g hi ho).2.2]
      rfl
    · rw [instructionSupport_eq g (Or.inr ho)]
      exact (Finset.insert_eq_of_mem (by simp)).symm
  · rw [instructionSupport_eq g (Or.inl hi)]
    exact (Finset.insert_eq_of_mem (by simp)).symm

theorem inverse_run (g : Layout ι) (r : ι → ZMod 2) :
    Circuit.run g.inverse (Circuit.run g.program r) = r := by
  apply run_reverse
  intro op hop
  obtain ⟨dst, src, hne, rfl⟩ := g.program_add op hop
  exact add_involutive dst src hne

theorem run_inverse (g : Layout ι) (r : ι → ZMod 2) :
    Circuit.run g.program (Circuit.run g.inverse r) = r := by
  have h := run_reverse g.program.reverse (fun op hop => by
    obtain ⟨dst, src, hne, rfl⟩ := g.program_add op (List.mem_reverse.mp hop)
    exact add_involutive dst src hne) r
  simpa [inverse] using h
/-- The finite instruction list is a permutation of all complete register
states; both directions are evaluated by the proved executable programs. -/
def equiv (g : Layout ι) : (ι → ZMod 2) ≃ (ι → ZMod 2) where
  toFun := Circuit.run g.program
  invFun := Circuit.run g.inverse
  left_inv := inverse_run g
  right_inv := run_inverse g

omit [DecidableEq ι] in
@[simp] theorem inverse_length (g : Layout ι) :
    g.inverse.length = g.inputs.length - 1 + (g.outputs.length - 1) := by
  rw [inverse, List.length_reverse, program_length]

end Layout
end IntegerMultBounds.Networks.ReversibleFanout
