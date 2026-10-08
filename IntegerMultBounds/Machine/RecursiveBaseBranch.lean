import IntegerMultBounds.Machine.RecursiveDigitRoleBank
import IntegerMultBounds.Machine.RecursiveWidthBranch

/-! Actual width-one base block in the three-PC finite controller. Recursive
entry remains a supplied same-bank program; no recursive correctness or global
termination is assumed by this base-case theorem. -/
namespace IntegerMultBounds.Machine.RecursiveBaseBranch
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveShiftRoleBank (common source updated)
variable {t u r : ℕ}

abbrev privateTapes := RecursiveDigitInterchangeConstruct.TapeCount prime+RecursiveDigitInterchangeConstruct.TapeCount prime
abbrev TapeCount (t u : ℕ) := t+(7+u)+privateTapes
abbrev baseStates := (fun {t s a : ℕ} (_ : Program t s a) => s)
  (RecursiveDigitInterchangeClean.program Shared50ModularControl.prime_prime.two_le)

def baseProgram (wire : Fin t) : Program (TapeCount t u) baseStates prime := RecursiveDigitRoleBank.program wire

def widthSlot (wire : Fin t) : Fin (TapeCount t u) :=
  Fin.castAdd privateTapes (RecursiveShiftRoleBank.commonPorts (u := u) wire (Fin.natAdd 2 (3 : Fin 6)))

theorem widthSlot_value (wire : Fin t) : (widthSlot (u := u) wire).val = t+4 := rfl

def family (wire : Fin t) (recur : Program (TapeCount t u) r prime) :=
  RecursiveWidthBranch.family (widthSlot wire) (baseProgram wire) recur

def program (wire : Fin t) (recur : Program (TapeCount t u) r prime)
    (baseExit : Fin baseStates → Option (Fin 3)) (recurExit : Fin r → Option (Fin 3)) :=
  RecursiveWidthBranch.program (widthSlot wire) (baseProgram wire) recur baseExit recurExit

theorem width_header (wire : Fin t) (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime) :
    (CleanSubbank.bank (s := privateTapes) (common roles hs aux)).head (widthSlot wire) = 1 ∧
    (CleanSubbank.bank (s := privateTapes) (common roles hs aux)).tape (widthSlot wire) =
      BinaryDescriptorStack.descriptor (hs 3) := by
  simp only [CleanSubbank.bank,common,widthSlot,RecursiveShiftRoleBank.commonPorts,
    Tapes.append,Fin.addCases_left,Fin.addCases_right,RecursiveShiftRoleBank.headers]
  exact ⟨trivial,(BinaryDescriptorStackRoundtrip.descriptor_encoded (hs 3)).symm⟩

/-- Guard entry followed by the actual digit machine, retaining its terminal
state inside PC one. Arbitrary base exits permit a later physical return edge. -/
theorem base_exact {v : Descriptor} (hw : v.width = 1) (wire : Fin t)
    (recur : Program (TapeCount t u) r prime)
    (baseExit : Fin baseStates → Option (Fin 3)) (recurExit : Fin r → Option (Fin 3))
    (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head wire = 0) (ht : roles.tape wire = source x)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    ∃ (k : ℕ) (c : Config (TapeCount t u) baseStates prime),
      k ≤ RecursiveDigitRoleBank.coefficient*volume prime v+3 ∧
      run (program wire recur baseExit recurExit) k
        ((CleanSubbank.bank (common roles hs aux)).start (program wire recur baseExit recurExit)) =
        some (c.mapState (FiniteFlow.embed (RecursiveWidthBranch.states baseStates r) 1)) ∧
      step (baseProgram wire) c = none ∧
      c.tapes = CleanSubbank.bank (common (updated roles wire (RecursiveDigitRoleBank.array hw x)) hs aux) := by
  have hheader := width_header wire roles hs aux
  obtain ⟨k,hk,hguard⟩ := RecursiveWidthBranch.enter_exact (widthSlot wire) (baseProgram wire) recur
    baseExit recurExit (CleanSubbank.bank (common roles hs aux)) (hs 3) hheader.1 hheader.2 (hv.2 3)
  have hvw : Counter.value (hs 3) = 1 := (hv.1 3).trans hw
  have hbranch : RecursiveWidthBranch.branch (Counter.value (hs 3)) = 1 := by
    rw [hvw]; rfl
  rw [hbranch] at hguard
  obtain ⟨n,c,hn,hr,hhalt,hpost⟩ := RecursiveDigitRoleBank.realizes hw wire roles hs aux x hh ht hv hpos
    (CleanSubbank.bank (common roles hs aux)) rfl
  have hrun := FiniteFlow.block_run (family wire recur) (RecursiveWidthBranch.next baseExit recurExit)
    0 1 n ((CleanSubbank.bank (common roles hs aux)).start (baseProgram wire)) c hr
  refine ⟨k+n,c,by omega,?_,hhalt,hpost⟩
  rw [run_add]
  change (run (RecursiveWidthBranch.program (widthSlot wire) (baseProgram wire) recur baseExit recurExit) k
    ((CleanSubbank.bank (common roles hs aux)).start _)).bind _ = _
  erw [hguard]
  simp only [Option.bind_some]
  exact hrun

/-- With base PC configured to halt, the concrete controller implements the
clean width-one interchange within its base bound plus three transitions. -/
theorem base_hoare {v : Descriptor} (hw : v.width = 1) (wire : Fin t)
    (recur : Program (TapeCount t u) r prime) (recurExit : Fin r → Option (Fin 3))
    (roles : Tapes t prime) (hs : Fin 6 → List Bool) (aux : Tapes u prime)
    (x : Fin (volume prime v) → Fin 4) (hh : roles.head wire = 0) (ht : roles.tape wire = source x)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    HoareTime (program wire recur (fun _ => none) recurExit)
      (fun w => w = CleanSubbank.bank (common roles hs aux))
      (fun w => w = CleanSubbank.bank (common (updated roles wire (RecursiveDigitRoleBank.array hw x)) hs aux))
      (RecursiveDigitRoleBank.coefficient*volume prime v+3) := by
  intro w hw'
  subst w
  obtain ⟨k,c,hk,hr,hh',he⟩ := base_exact hw wire recur (fun _ => none) recurExit roles hs aux x hh ht hv hpos
  refine ⟨k,c.mapState (FiniteFlow.embed (RecursiveWidthBranch.states baseStates r) 1),hk,hr,?_,he⟩
  exact FiniteFlow.halt (family wire recur) (RecursiveWidthBranch.next (fun _ => none) recurExit)
    0 1 c hh' (by rfl)

end
end IntegerMultBounds.Machine.RecursiveBaseBranch
