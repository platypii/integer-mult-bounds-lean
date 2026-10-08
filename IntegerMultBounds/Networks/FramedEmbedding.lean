import IntegerMultBounds.Networks.BoundedFramedCircuit
import IntegerMultBounds.Networks.GlobalCircuit

/-! Injective placement of physical frame instructions into a larger register
file. Every edge and scalar instruction is retained, with exact local execution
and spectator preservation. -/

namespace IntegerMultBounds.Networks.FramedEmbedding

open FramedCircuit

variable {ι κ R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- Place the actual physical instruction at its injectively renamed roles. -/
def instruction (f : ι ↪ κ) : Instruction ι R E → Instruction κ R E
  | .edge i old next => .edge (f i) old next
  | .gate gate => .gate (GlobalCircuit.embedGate f gate)

/-- No instruction is removed or replaced by a default register. -/
def embed (f : ι ↪ κ) (instructions : List (Instruction ι R E)) :
    List (Instruction κ R E) := instructions.map (instruction f)

@[simp] theorem embed_length (f : ι ↪ κ) (instructions : List (Instruction ι R E)) :
    (embed f instructions).length = instructions.length := List.length_map _

theorem erase_embed (f : ι ↪ κ) (instructions : List (Instruction ι R E)) :
    BoundedFramedCircuit.erase (embed f instructions) =
      GlobalCircuit.embed f (BoundedFramedCircuit.erase instructions) := by
  induction instructions with
  | nil => rfl
  | cons instr rest ih =>
    cases instr <;> simp only [embed,List.map_cons,instruction,
      BoundedFramedCircuit.erase,List.filterMap_cons,GlobalCircuit.embed] at *
    · exact ih
    · exact congrArg (List.cons _) ih

section Execution
variable [DecidableEq ι] [DecidableEq κ]

theorem moduleGate_embed (f : ι ↪ κ) (gate : Circuit.Gate ι R) (state : κ → E) :
    moduleGate (GlobalCircuit.embedGate f gate) state ∘ f = moduleGate gate (state ∘ f) := by
  funext i
  simp only [moduleGate,GlobalCircuit.embedGate,List.map_map,Function.comp_apply]
  by_cases hi : i = gate.target
  · subst i; simp [Function.comp_def]
  · simp [Function.update_of_ne hi,Function.update_of_ne (f.injective.ne hi)]

theorem moduleRun_embed (f : ι ↪ κ) (program : Circuit.Program ι R) (state : κ → E) :
    moduleRun (GlobalCircuit.embed f program) state ∘ f = moduleRun program (state ∘ f) := by
  induction program generalizing state with
  | nil => rfl
  | cons gate rest ih =>
    simp only [GlobalCircuit.embed,List.map_cons,moduleRun_cons] at *
    rw [ih,moduleGate_embed]

theorem execute_embed (f : ι ↪ κ) (instr : Instruction ι R E) (state : κ → E) :
    execute (instruction f instr) state ∘ f = execute instr (state ∘ f) := by
  cases instr with
  | gate gate => exact moduleGate_embed f gate state
  | edge i old next =>
    funext j
    simp only [instruction,execute,Function.comp_apply]
    by_cases hj : j = i
    · subst j; simp
    · simp [Function.update_of_ne hj,Function.update_of_ne (f.injective.ne hj)]

/-- Running the placed instructions agrees exactly on the entire local bank. -/
theorem embed_run (f : ι ↪ κ) (instructions : List (Instruction ι R E)) (state : κ → E) :
    run (embed f instructions) state ∘ f = run instructions (state ∘ f) := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instr rest ih =>
    simp only [embed,List.map_cons,run_cons] at *
    rw [ih,execute_embed]

omit [DecidableEq ι] in
theorem execute_outside (f : ι ↪ κ) (instr : Instruction ι R E) (state : κ → E)
    (k : κ) (hk : ∀ i, f i ≠ k) : execute (instruction f instr) state k = state k := by
  cases instr with
  | gate gate => exact Function.update_of_ne (hk gate.target).symm _ _
  | edge i old next => exact Function.update_of_ne (hk i).symm _ _

omit [DecidableEq ι] in
/-- Every role outside the embedded bank keeps its original stored value. -/
theorem embed_outside (f : ι ↪ κ) (instructions : List (Instruction ι R E)) (state : κ → E)
    (k : κ) (hk : ∀ i, f i ≠ k) : run (embed f instructions) state k = state k := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instr rest ih =>
    simp only [embed,List.map_cons,run_cons] at *
    rw [ih,execute_outside f instr state k hk]

omit [DecidableEq ι] in
theorem moduleRun_outside (f : ι ↪ κ) (program : Circuit.Program ι R) (state : κ → E)
    (k : κ) (hk : ∀ i, f i ≠ k) : moduleRun (GlobalCircuit.embed f program) state k = state k := by
  apply moduleRun_preserves
  intro gate hg
  obtain ⟨localGate,_,rfl⟩ := List.mem_map.mp hg
  exact hk localGate.target

/-- Transfer a local physical identity to its actual placed execution. -/
theorem embed_identity (f : ι ↪ κ) (instructions : List (Instruction ι R E))
    (program : Circuit.Program ι R) (current desired : ι → Frame R E)
    (h : ∀ stored, run instructions stored = encode desired (moduleRun program (decode current stored)))
    (state : κ → E) :
    run (embed f instructions) state ∘ f =
      encode desired (moduleRun program (decode current (state ∘ f))) := by
  rw [embed_run,h]

/-- A placed physical identity on the complete register file, when spectator
frames remain fixed. No assumption is made on spectator stored contents. -/
theorem embed_identity_full (f : ι ↪ κ) (instructions : List (Instruction ι R E))
    (program : Circuit.Program ι R) (current desired : κ → Frame R E)
    (h : ∀ stored, run instructions stored =
      encode (desired ∘ f) (moduleRun program (decode (current ∘ f) stored)))
    (outside : ∀ k, (∀ i, f i ≠ k) → desired k = current k) (state : κ → E) :
    run (embed f instructions) state =
      encode desired (moduleRun (GlobalCircuit.embed f program) (decode current state)) := by
  funext k
  by_cases hk : ∃ i, f i = k
  · obtain ⟨i,rfl⟩ := hk
    have hl := congrFun (embed_identity f instructions program (current ∘ f) (desired ∘ f) h state) i
    have hm := congrFun (moduleRun_embed f program (decode current state)) i
    change moduleRun (GlobalCircuit.embed f program) (decode current state) (f i) =
      moduleRun program (decode (current ∘ f) (state ∘ f)) i at hm
    change run (embed f instructions) state (f i) =
      desired (f i) (moduleRun (GlobalCircuit.embed f program) (decode current state) (f i))
    rw [hm]
    exact hl
  · have hout : ∀ i, f i ≠ k := by simpa using hk
    rw [embed_outside f instructions state k hout]
    simp only [encode,moduleRun_outside f program (decode current state) k hout,
      outside k hout,decode,LinearEquiv.apply_symm_apply]

end Execution
end IntegerMultBounds.Networks.FramedEmbedding
