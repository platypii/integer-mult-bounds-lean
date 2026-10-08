import IntegerMultBounds.Machine.RecursiveCountedCallBoundary
import IntegerMultBounds.Machine.RecursiveRoleChildCallSetup

/-! Fixed permanent recursive-call bank: roles, shared scratch, six headers,
clock/count/payload-stack, auxiliary spectators, and descriptor/PC stacks. -/
namespace IntegerMultBounds.Machine.RecursiveCallBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveShiftRoleBank (common)
variable {t u : ℕ}

abbrev TapeCount (t u : ℕ) := t+(7+((3+u)+2))

def controlSlot (i : Fin 3) : Fin (TapeCount t u) :=
  Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd 2 (Fin.castAdd u i)))

def headerSlot (i : Fin 6) : Fin (TapeCount t u) :=
  Fin.natAdd t (Fin.castAdd ((3+u)+2) (Fin.natAdd 1 i))

def layout : RoleArrayFrames.Layout (TapeCount t u) where
  stack := controlSlot 2
  clock := controlSlot 0
  count := controlSlot 1
  stack_clock := by simp [controlSlot,Fin.ext_iff]
  stack_count := by simp [controlSlot,Fin.ext_iff]
  clock_count := by simp [controlSlot,Fin.ext_iff]

def role (i : Fin t) : RoleArrayFrames.Role (layout (t := t) (u := u)) :=
  ⟨Fin.castAdd (7+((3+u)+2)) i,by
    have hi := i.isLt
    constructor
    · intro h; have he := congrArg Fin.val h; simp only [layout,controlSlot,Fin.val_castAdd,Fin.val_natAdd] at he; omega
    constructor <;> intro h <;> have he := congrArg Fin.val h <;>
      simp only [layout,controlSlot,Fin.val_castAdd,Fin.val_natAdd] at he <;> omega⟩

theorem role_injective : Function.Injective (role (t := t) (u := u)) := by
  intro i j h
  exact Fin.castAdd_injective _ _ (congrArg Subtype.val h)

def countSlots : Fin 8 → Fin (TapeCount t u) := fun i =>
  Fin.addCases (motive := fun _ => Fin (TapeCount t u))
    (fun j : Fin 2 => controlSlot (Fin.castAdd 1 j)) headerSlot i

theorem countSlots_injective : Function.Injective (countSlots (t := t) (u := u)) := by
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp_all [countSlots,Fin.addCases,controlSlot,headerSlot,Fin.ext_iff]

def work (f : ℤ → Fin (prime+4)) (p : ℤ) : Tapes 3 prime :=
  ⟨![0,0,p],![fun _ => blank,fun _ => blank,f]⟩

def bank (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) : Tapes (TapeCount t u) prime :=
  common roles hs (((work f p).append aux).append st)

theorem ready (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) : RecursiveCallCount.Ready countSlots hs (bank roles hs f p aux st) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals try {simp [bank,common,countSlots,Fin.addCases,controlSlot,Tapes.append,work,show ¬ 3+u ≤ 1 by omega]}
  intro j
  simp only [bank,common,countSlots,headerSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  exact ⟨rfl,rfl⟩

theorem payload_stack (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    (bank roles hs f p aux st).head (controlSlot 2) = p ∧
    (bank roles hs f p aux st).tape (controlSlot 2) = f := by
  simp only [bank,common,controlSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,work]
  exact ⟨rfl,rfl⟩

def rolePart (v : Tapes (TapeCount t u) prime) : Tapes t prime :=
  ⟨fun i => v.head (role (u := u) i).val,fun i => v.tape (role (u := u) i).val⟩

private theorem bank_repack (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (aux : Tapes u prime) (st : Tapes 2 prime)
    (v : Tapes (TapeCount t u) prime)
    (hf : ∀ i, t ≤ i.val → i ≠ controlSlot 2 →
      v.head i = (bank roles hs f p aux st).head i ∧ v.tape i = (bank roles hs f p aux st).tape i) :
    v = bank (rolePart v) hs (v.tape (controlSlot 2)) (v.head (controlSlot 2)) aux st := by
  have point (i : Fin (TapeCount t u)) :
      v.head i = (bank (rolePart v) hs (v.tape (controlSlot 2)) (v.head (controlSlot 2)) aux st).head i ∧
      v.tape i = (bank (rolePart v) hs (v.tape (controlSlot 2)) (v.head (controlSlot 2)) aux st).tape i := by
    induction i using Fin.addCases with
    | left i => simp only [bank,common,Tapes.append,Fin.addCases_left]; exact ⟨rfl,rfl⟩
    | right i =>
      have hlow : t ≤ (Fin.natAdd t i).val := by simp only [Fin.val_natAdd]; omega
      induction i using Fin.addCases with
      | left i =>
        have hn : Fin.natAdd t (Fin.castAdd ((3+u)+2) i) ≠ controlSlot 2 := by
          intro h; have he := congrArg Fin.val h; have hi := i.isLt
          simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd] at he; omega
        simpa only [bank,common,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hf _ hlow hn
      | right i =>
        induction i using Fin.addCases with
        | right i =>
          have hn : Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd (3+u) i)) ≠ controlSlot 2 := by
            intro h; have he := congrArg Fin.val h
            simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd] at he; omega
          simpa only [bank,common,Tapes.append,Fin.addCases_right] using hf _ hlow hn
        | left i =>
          induction i using Fin.addCases with
          | right i =>
            have hn : Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd 2 (Fin.natAdd 3 i))) ≠ controlSlot 2 := by
              intro h; have he := congrArg Fin.val h
              simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd] at he; omega
            simpa only [bank,common,Tapes.append,Fin.addCases_right,Fin.addCases_left] using hf _ hlow hn
          | left i =>
            fin_cases i
            · have h := hf (controlSlot 0) (by simp [controlSlot]) (by simp [controlSlot,Fin.ext_iff])
              simpa [bank,common,controlSlot,Tapes.append,Fin.addCases,work] using h
            · have h := hf (controlSlot 1) (by simp [controlSlot]) (by simp [controlSlot,Fin.ext_iff])
              simpa [bank,common,controlSlot,Tapes.append,Fin.addCases,work] using h
            · simp [bank,common,controlSlot,Tapes.append,Fin.addCases,work,show ¬ 3+u ≤ 2 by omega]
  cases v with
  | mk vh vt => exact congrArg₂ Tapes.mk (funext fun i => (point i).1) (funext fun i => (point i).2)

/-- The pure endpoint of the actual payload entry is again the same permanent
layout, with only role tapes and the payload stack changed. -/
theorem entered_bank (ops : List (Fin t)) (src dst : Fin t) (n : ℕ)
    (roles : Tapes t prime) (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    let v := RoleArrayCall.entered layout (ops.map role) (role src) (role dst) n (bank roles hs f p aux st)
    v = bank (rolePart v) hs (v.tape (controlSlot 2)) (v.head (controlSlot 2)) aux st := by
  dsimp only
  apply bank_repack roles hs f p aux st
  intro i hlo hne
  have hrole (j : Fin t) : i ≠ (role (u := u) j).val := by
    intro h; have he := congrArg Fin.val h; have hj := j.isLt
    simp only [role,Fin.val_castAdd] at he; omega
  have hf := RoleArrayFrames.saved_frame layout (ops.map role) n (bank roles hs f p aux st) i hne (by
    intro j hj; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hj; exact hrole j)
  simpa [RoleArrayCall.entered,RoleArrayMove.moved,RoleArrayCall.slots,SharedPlacementAlphabet.setTape,hrole] using hf

end
end IntegerMultBounds.Machine.RecursiveCallBank
