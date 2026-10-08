import IntegerMultBounds.Machine.BinaryDescriptorFrameRestore
import IntegerMultBounds.Machine.RecursiveAffinePrepare

/-! Six-header push and occupied-header restoration on one dedicated stack.
The programs are fixed independently of words or lengths. The stack may contain
older data; only the explicit free interval for the saved frame is required. -/
namespace IntegerMultBounds.Machine.RecursiveViewFrame
open BinaryDescriptorFrames
variable {q : ℕ}

abbrev stack : Fin 7 := 6

def slot (i : Fin 6) : Slot stack := ⟨Fin.castAdd 1 i,by
  intro h
  have hh := congrArg Fin.val h
  have hi := i.isLt
  simp only [Fin.val_castAdd] at hh
  change i.val = 6 at hh
  omega⟩

def fields : List (Slot stack) := List.ofFn slot

theorem fields_nodup : fields.Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  exact Fin.castAdd_injective _ _ (congrArg Subtype.val h)

def words (hs : Fin 6 → List Bool) : Fin 7 → List Bool :=
  fun i => Fin.addCases (motive := fun _ => List Bool) hs (fun _ : Fin 1 => []) i

def bank (hs : Fin 6 → List Bool) (st : Tapes 1 q) : Tapes 7 q :=
  (⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (hs i)⟩ : Tapes 6 q).append st

def savedStack (hs : Fin 6 → List Bool) (st : Tapes 1 q) : Tapes 1 q :=
  let v := saved stack fields (words hs) (bank hs st)
  ⟨fun _ => v.head stack,fun _ => v.tape stack⟩

@[simp] theorem words_slot (hs : Fin 6 → List Bool) (i : Fin 6) : words hs (slot i) = hs i := by
  simp only [words,slot,Fin.addCases_left]

@[simp] theorem bank_head_slot (hs : Fin 6 → List Bool) (st : Tapes 1 q) (i : Fin 6) : (bank hs st).head (slot i) = 1 := by
  simp only [bank,slot,Tapes.append,Fin.addCases_left]

@[simp] theorem bank_tape_slot (hs : Fin 6 → List Bool) (st : Tapes 1 q) (i : Fin 6) :
    (bank hs st).tape (slot i) = RadixZeroFill.encodedBinary (hs i) := by
  simp only [bank,slot,Tapes.append,Fin.addCases_left]

theorem field_mem (i : Fin 6) : slot i ∈ fields := List.mem_ofFn.mpr ⟨i,rfl⟩
theorem mem_fields (i : Slot stack) : i ∈ fields ↔ ∃ j, slot j = i := List.mem_ofFn
theorem fields_length : fields.length = 6 := List.length_ofFn

attribute [local irreducible] fields

private theorem saved_stack_congr (ops : List (Slot stack)) (xs : Fin 7 → List Bool) (v w : Tapes 7 q)
    (hh : v.head stack = w.head stack) (ht : v.tape stack = w.tape stack) :
    (saved stack ops xs v).head stack = (saved stack ops xs w).head stack ∧
    (saved stack ops xs v).tape stack = (saved stack ops xs w).tape stack := by
  induction ops generalizing v w with
  | nil => exact ⟨hh,ht⟩
  | cons op ops ih =>
    exact ih (write stack op xs v) (write stack op xs w)
      (by simp only [write,SharedPlacementAlphabet.setTape,Function.update_self,hh])
      (by simp only [write,SharedPlacementAlphabet.setTape,Function.update_self,hh,ht])

theorem saved_bank (old hs : Fin 6 → List Bool) (st : Tapes 1 q) :
    saved stack fields (words old) (bank hs st) = bank hs (savedStack old st) := by
  have he := saved_stack_congr fields (words old) (bank hs st) (bank old st) rfl rfl
  apply congrArg₂ Tapes.mk <;> funext i
  · change Fin (6+1) at i
    induction i using Fin.addCases with
    | left i => simpa only [slot,bank,Tapes.append,Fin.addCases_left] using (saved_frame stack fields (words old) (bank hs st) (slot i) (slot i).property).1
    | right i => fin_cases i; exact he.1
  · change Fin (6+1) at i
    induction i using Fin.addCases with
    | left i => simpa only [slot,bank,Tapes.append,Fin.addCases_left] using (saved_frame stack fields (words old) (bank hs st) (slot i) (slot i).property).2
    | right i => fin_cases i; exact he.2

theorem restored_bank (old hs : Fin 6 → List Bool) (st : Tapes 1 q) :
    restored fields (words old) (bank hs st) = bank old st := by
  apply congrArg₂ Tapes.mk <;> funext i
  · change Fin (6+1) at i
    induction i using Fin.addCases with
    | left i => simpa only [slot,bank,Tapes.append,Fin.addCases_left] using (restored_field fields fields_nodup (words old) (bank hs st) (slot i) (field_mem i)).1
    | right i => fin_cases i; exact (restored_stack fields (words old) (bank hs st)).1
  · change Fin (6+1) at i
    induction i using Fin.addCases with
    | left i =>
      have hh := (restored_field fields fields_nodup (words old) (bank hs st) (slot i) (field_mem i)).2
      rw [words_slot] at hh
      simpa only [bank,slot,Tapes.append,Fin.addCases_left] using hh.trans (BinaryDescriptorStackRoundtrip.descriptor_encoded (old i))
    | right i => fin_cases i; exact (restored_stack fields (words old) (bank hs st)).2

noncomputable def pushProgram := BinaryDescriptorFrames.pushProgram (a := q) stack fields
noncomputable def restoreProgram := BinaryDescriptorFrameRestore.program (a := q) stack fields

def pushCost (hs : Fin 6 → List Bool) := BinaryDescriptorFrames.cost fields (words hs)
def restoreCost (old hs : Fin 6 → List Bool) :=
  BinaryDescriptorCleanupList.cost (BinaryDescriptorFrameRestore.slots fields) (words hs)+1+pushCost old

theorem push_hoare (hs : Fin 6 → List Bool) (st : Tapes 1 q) :
    HoareTime (pushProgram (q := q)) (fun w => w = bank hs st)
      (fun w => w = bank hs (savedStack hs st)) (pushCost hs) := by
  have hh := BinaryDescriptorFrames.push_hoare stack fields (words hs) (bank hs st) (by
    intro i hi
    obtain ⟨j,rfl⟩ := (mem_fields _).mp hi
    simpa only [bank_head_slot,bank_tape_slot,words_slot] using
      (show (1 : ℤ) = 1 ∧ RadixZeroFill.encodedBinary (hs j) = BinaryDescriptorStack.descriptor (hs j) from
        ⟨rfl,(BinaryDescriptorStackRoundtrip.descriptor_encoded (hs j)).symm⟩))
  simpa only [pushProgram,pushCost,saved_bank] using hh

def Free (hs : Fin 6 → List Bool) (st : Tapes 1 q) : Prop :=
  ∀ z, st.head 0 ≤ z → z < st.head 0+span fields (words hs) → st.tape 0 z = blank

theorem restore_hoare (old hs : Fin 6 → List Bool) (st : Tapes 1 q) (hf : Free old st) :
    HoareTime (restoreProgram (q := q)) (fun w => w = bank hs (savedStack old st))
      (fun w => w = bank old st) (restoreCost old hs) := by
  have hh := BinaryDescriptorFrameRestore.restore_hoare stack fields fields_nodup (words old) (words hs) (bank hs st)
    (by intro i hi; obtain ⟨j,rfl⟩ := (mem_fields _).mp hi
        simpa only [bank_head_slot,bank_tape_slot,words_slot] using
      (show (1 : ℤ) = 1 ∧ RadixZeroFill.encodedBinary (hs j) = BinaryDescriptorStack.descriptor (hs j) from
        ⟨rfl,(BinaryDescriptorStackRoundtrip.descriptor_encoded (hs j)).symm⟩)) hf
  simpa only [restoreProgram,restoreCost,pushCost,saved_bank,restored_bank] using hh

theorem free_empty (hs : Fin 6 → List Bool) : Free hs (SharedBank.empty 1 q) := by
  intro z _ _
  rfl

theorem pushCost_le (hs : Fin 6 → List Bool) (L : ℕ) (hL : ∀ i, (hs i).length ≤ L) :
    pushCost hs ≤ 12*L+48 := by
  exact BinaryDescriptorFrames.six_field_cost fields fields_length (words hs) L
    (by intro i hi; obtain ⟨j,rfl⟩ := (mem_fields _).mp hi; simpa only [words_slot] using hL j)

theorem restoreCost_le (old hs : Fin 6 → List Bool) (L : ℕ)
    (ho : ∀ i, (old i).length ≤ L) (hh : ∀ i, (hs i).length ≤ L) : restoreCost old hs ≤ 24*L+79 := by
  have hp := pushCost_le old L ho
  have hc := BinaryDescriptorCleanupList.cost_le (BinaryDescriptorFrameRestore.slots fields) (words hs) L
    (by intro i hi; obtain ⟨op,hop,rfl⟩ := List.mem_map.mp hi
        obtain ⟨j,rfl⟩ := (mem_fields _).mp hop; simpa only [words_slot] using hh j)
  simp only [BinaryDescriptorFrameRestore.slots,List.length_map,fields,List.length_ofFn] at hc
  unfold restoreCost BinaryDescriptorFrameRestore.slots fields
  omega

end IntegerMultBounds.Machine.RecursiveViewFrame
