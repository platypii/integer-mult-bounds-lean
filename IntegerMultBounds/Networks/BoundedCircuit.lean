import IntegerMultBounds.Networks.Circuit

/-! Restrict a scalar program to the finite register interval proved to contain
every target and source. No out-of-range register is defaulted or identified. -/

namespace IntegerMultBounds.Networks.BoundedCircuit

open Circuit

variable {R : Type*}

/-- Every register actually mentioned by an elementary update is in range. -/
def GateBounded (capacity : ℕ) (gate : Gate ℕ R) : Prop :=
  gate.target < capacity ∧ ∀ term ∈ gate.terms, term.1 < capacity

def Bounded (capacity : ℕ) (program : Program ℕ R) : Prop :=
  ∀ gate ∈ program, GateBounded capacity gate

/-- Replace every certified natural register by that same finite register. -/
def finiteGate (capacity : ℕ) (gate : Gate ℕ R) (h : GateBounded capacity gate) : Gate (Fin capacity) R :=
  ⟨⟨gate.target, h.1⟩, gate.terms.attach.map (fun term => (⟨term.val.1, h.2 term.val term.property⟩, term.val.2))⟩

/-- Retain the complete instruction list while making register bounds intrinsic. -/
def finiteProgram (capacity : ℕ) (program : Program ℕ R) (h : Bounded capacity program) :
    Program (Fin capacity) R :=
  program.attach.map (fun gate => finiteGate capacity gate.val (h gate.val gate.property))

@[simp] theorem finiteProgram_length (capacity : ℕ) (program : Program ℕ R) (h : Bounded capacity program) :
    (finiteProgram capacity program h).length = program.length := by
  simp [finiteProgram]

@[simp] theorem finiteProgram_nil (capacity : ℕ) (h : Bounded capacity ([] : Program ℕ R)) :
    finiteProgram capacity [] h = [] := rfl

@[simp] theorem finiteProgram_cons (capacity : ℕ) (gate : Gate ℕ R) (program : Program ℕ R)
    (h : Bounded capacity (gate :: program)) :
    finiteProgram capacity (gate :: program) h =
      finiteGate capacity gate (h gate (by simp)) ::
        finiteProgram capacity program (fun g hg => h g (List.mem_cons_of_mem gate hg)) := by
  simp [finiteProgram, List.attach_cons, List.map_map, Function.comp_def]

/-- Restriction commutes with reversal of the literal instruction list. -/
theorem finiteProgram_reverse (capacity : ℕ) (program : Program ℕ R) (h : Bounded capacity program) :
    finiteProgram capacity program.reverse (fun g hg => h g (List.mem_reverse.mp hg)) =
      (finiteProgram capacity program h).reverse := by
  simp [finiteProgram, List.attach_reverse, List.map_reverse, List.map_map, Function.comp_def]

variable [CommRing R]

/-- Each scalar update agrees with restriction of the original register state. -/
theorem finiteGate_run (capacity : ℕ) (gate : Gate ℕ R) (h : GateBounded capacity gate) (state : ℕ → R) :
    (finiteGate capacity gate h).run (fun i => state i.val) = fun i => gate.run state i.val := by
  funext i
  simp only [finiteGate, Gate.run, List.map_map, Function.comp_def]
  have hsum :
      (gate.terms.attach.map (fun term => term.val.2 * state term.val.1)).sum =
        (gate.terms.map (fun term => term.2 * state term.1)).sum := by
    congr 1
    exact List.attach_map_val (f := fun term : ℕ × R => term.2 * state term.1)
  rw [hsum]
  by_cases hi : i.val = gate.target
  · have he : i = (⟨gate.target, h.1⟩ : Fin capacity) := Fin.ext hi
    subst i
    simp
  · have he : i ≠ (⟨gate.target, h.1⟩ : Fin capacity) := fun he => hi (congrArg Fin.val he)
    simp only [Function.update_of_ne hi, Function.update_of_ne he]

/-- The complete finite program executes exactly the bounded part of the
original natural-register program, for every initial register state. -/
theorem finiteProgram_run (capacity : ℕ) (program : Program ℕ R) (h : Bounded capacity program)
    (state : ℕ → R) :
    Circuit.run (finiteProgram capacity program h) (fun i => state i.val) =
      fun i => Circuit.run program state i.val := by
  induction program generalizing state with
  | nil => rfl
  | cons gate program ih =>
    rw [finiteProgram_cons, Circuit.run_cons, finiteGate_run]
    exact ih _ (gate.run state)

theorem finiteProgram_reverse_run (capacity : ℕ) (program : Program ℕ R)
    (h : Bounded capacity program) (state : ℕ → R) :
    Circuit.run (finiteProgram capacity program h).reverse (fun i => state i.val) =
      fun i => Circuit.run program.reverse state i.val := by
  rw [← finiteProgram_reverse]
  exact finiteProgram_run _ _ _ _

end IntegerMultBounds.Networks.BoundedCircuit
