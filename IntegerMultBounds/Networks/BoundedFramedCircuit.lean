import IntegerMultBounds.Networks.BoundedCircuit
import IntegerMultBounds.Networks.FramedCircuit

/-! Checked restriction of physical frame instructions and scalar module
execution to a finite register bank. Every instruction and incidence survives. -/

namespace IntegerMultBounds.Networks.BoundedFramedCircuit

open FramedCircuit BoundedCircuit
variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

theorem finiteGate_module (capacity : ℕ) (gate : Circuit.Gate ℕ R)
    (h : GateBounded capacity gate) (state : ℕ → E) :
    moduleGate (finiteGate capacity gate h) (fun i => state i.val) = fun i => moduleGate gate state i.val := by
  funext i
  simp only [finiteGate, moduleGate, List.map_map, Function.comp_def]
  have hs : (gate.terms.attach.map (fun term => term.val.2 • state term.val.1)).sum =
      (gate.terms.map (fun term => term.2 • state term.1)).sum :=
    congrArg List.sum (List.attach_map_val (f := fun term : ℕ × R => term.2 • state term.1))
  rw [hs]
  by_cases hi : i.val = gate.target
  · have he : i = (⟨gate.target,h.1⟩ : Fin capacity) := Fin.ext hi
    subst i
    simp
  · have he : i ≠ (⟨gate.target,h.1⟩ : Fin capacity) := fun he => hi (congrArg Fin.val he)
    simp only [Function.update_of_ne hi,Function.update_of_ne he]

theorem finiteProgram_module (capacity : ℕ) (program : Circuit.Program ℕ R)
    (h : BoundedCircuit.Bounded capacity program) (state : ℕ → E) :
    moduleRun (finiteProgram capacity program h) (fun i => state i.val) =
      fun i => moduleRun program state i.val := by
  induction program generalizing state with
  | nil => rfl
  | cons gate program ih =>
    rw [finiteProgram_cons,moduleRun_cons,finiteGate_module]
    exact ih _ (moduleGate gate state)

def InstructionBounded (capacity : ℕ) : Instruction ℕ R E → Prop
  | .edge i _ _ => i < capacity
  | .gate gate => GateBounded capacity gate

def Bounded (capacity : ℕ) (instructions : List (Instruction ℕ R E)) : Prop :=
  ∀ instruction ∈ instructions, InstructionBounded capacity instruction

def finiteInstruction (capacity : ℕ) (instruction : Instruction ℕ R E)
    (h : InstructionBounded capacity instruction) : Instruction (Fin capacity) R E :=
  match instruction with
  | .edge i old next => .edge ⟨i,h⟩ old next
  | .gate gate => .gate (finiteGate capacity gate h)

def restrict (capacity : ℕ) (instructions : List (Instruction ℕ R E)) (h : Bounded capacity instructions) :
    List (Instruction (Fin capacity) R E) :=
  instructions.attach.map (fun instr => finiteInstruction capacity instr.val (h instr.val instr.property))

@[simp] theorem restrict_length (capacity : ℕ) (instructions : List (Instruction ℕ R E))
    (h : Bounded capacity instructions) : (restrict capacity instructions h).length = instructions.length := by
  simp [restrict]

theorem restrict_nil (capacity : ℕ) (h : Bounded capacity ([] : List (Instruction ℕ R E))) :
    restrict capacity [] h = [] := rfl

theorem restrict_cons (capacity : ℕ) (instr : Instruction ℕ R E) (rest : List (Instruction ℕ R E))
    (h : Bounded capacity (instr::rest)) :
    restrict capacity (instr::rest) h = finiteInstruction capacity instr (h instr (by simp)) ::
      restrict capacity rest (fun i hi => h i (List.mem_cons_of_mem instr hi)) := by
  simp [restrict,List.attach_cons,List.map_map,Function.comp_def]

theorem finiteInstruction_execute (capacity : ℕ) (instruction : Instruction ℕ R E)
    (h : InstructionBounded capacity instruction) (state : ℕ → E) :
    execute (finiteInstruction capacity instruction h) (fun i => state i.val) =
      fun i => execute instruction state i.val := by
  cases instruction with
  | gate gate => exact finiteGate_module capacity gate h state
  | edge r old next =>
    funext i
    change Function.update (fun i : Fin capacity => state i.val) ⟨r,h⟩ _ i = Function.update state r _ i.val
    by_cases hi : i.val = r
    · have he : i = (⟨r,h⟩ : Fin capacity) := Fin.ext hi
      subst i
      simp
    · have he : i ≠ (⟨r,h⟩ : Fin capacity) := fun he => hi (congrArg Fin.val he)
      simp only [Function.update_of_ne hi,Function.update_of_ne he]

/-- Every physical edge and scalar update commutes with finite restriction. -/
theorem restrict_run (capacity : ℕ) (instructions : List (Instruction ℕ R E))
    (h : Bounded capacity instructions) (state : ℕ → E) :
    run (restrict capacity instructions h) (fun i => state i.val) =
      fun i => run instructions state i.val := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instr rest ih =>
    rw [restrict_cons,run_cons,finiteInstruction_execute]
    exact ih _ (execute instr state)

/-- Erase physical frame changes but retain all elementary scalar instructions. -/
def erase {ι : Type*} (instructions : List (Instruction ι R E)) : Circuit.Program ι R :=
  instructions.filterMap (fun instr => match instr with | .edge _ _ _ => none | .gate g => some g)

theorem erase_bounded (capacity : ℕ) (instructions : List (Instruction ℕ R E))
    (h : Bounded capacity instructions) : BoundedCircuit.Bounded capacity (erase instructions) := by
  intro gate hg
  obtain ⟨instr,hi,he⟩ := List.mem_filterMap.mp hg
  cases instr with
  | edge i old next => simp at he
  | gate g =>
    have he' : g = gate := by simpa using he
    subst gate
    exact h _ hi

/-- Erasure and restriction commute exactly, not just at execution level. -/
theorem erase_restrict (capacity : ℕ) (instructions : List (Instruction ℕ R E))
    (h : Bounded capacity instructions) :
    erase (restrict capacity instructions h) =
      finiteProgram capacity (erase instructions) (erase_bounded capacity instructions h) := by
  induction instructions with
  | nil => rfl
  | cons instr rest ih =>
    rw [restrict_cons]
    cases instr with
    | edge i old next => simpa only [erase,finiteInstruction,List.filterMap_cons] using ih _
    | gate gate =>
      simp only [erase,finiteInstruction,List.filterMap_cons]
      rw [finiteProgram_cons]
      congr 1
      exact ih _

omit [CommRing R] in
theorem finiteProgram_congr (capacity : ℕ) (left right : Circuit.Program ℕ R)
    (hl : BoundedCircuit.Bounded capacity left) (hr : BoundedCircuit.Bounded capacity right)
    (he : left = right) : finiteProgram capacity left hl = finiteProgram capacity right hr := by
  subst right
  rfl

/-- Transfer a proved physical decode/run/encode identity to arbitrary finite
stored states. The extension outside the bank is only used in the proof. -/
theorem restrict_identity (capacity : ℕ) (instructions : List (Instruction ℕ R E))
    (hi : Bounded capacity instructions) (program : Circuit.Program ℕ R)
    (hp : BoundedCircuit.Bounded capacity program) (current desired : ℕ → Frame R E)
    (hrun : ∀ state, run instructions state = encode desired (moduleRun program (decode current state)))
    (stored : Fin capacity → E) :
    run (restrict capacity instructions hi) stored =
      encode (fun i => desired i.val)
        (moduleRun (finiteProgram capacity program hp) (decode (fun i => current i.val) stored)) := by
  let full : ℕ → E := fun i => if hi : i < capacity then stored ⟨i,hi⟩ else 0
  have he : (fun i : Fin capacity => full i.val) = stored := by
    funext i
    simp [full,i.isLt]
  rw [← he,restrict_run,hrun]
  change (fun i => desired i.val (moduleRun program (decode current full) i.val)) =
    encode (fun i => desired i.val)
      (moduleRun (finiteProgram capacity program hp) (fun i => decode current full i.val))
  rw [finiteProgram_module]
  rfl

end IntegerMultBounds.Networks.BoundedFramedCircuit
