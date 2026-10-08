import IntegerMultBounds.Machine.RecursiveChildCallSetup
import IntegerMultBounds.Machine.RecursiveStackAllocation
import IntegerMultBounds.Machine.RecursiveCleanReturn

/-! Physical return on the exact forty-tape child-preparation bank. Retained
child headers are erased before saved parent headers are popped; the PC frame
is retained for the actual decoder. No header assignment is a free operation. -/
namespace IntegerMultBounds.Machine.RecursiveChildCallReturn
open RecursiveChildCallSetup BinaryDescriptorFrames
open SharedPlacementAlphabet (setTape)
variable {q k : ℕ}

private theorem fields_nodup : fields.Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j h
  have he := congrArg (fun x : Slot descriptorStack => x.val.val) h
  simp only [header] at he
  exact Fin.ext (by omega)

private theorem mem_fields (i : Slot descriptorStack) : i ∈ fields ↔ ∃ j, header j = i := List.mem_ofFn

attribute [local irreducible] fields

private theorem header_bank (hs : Fin 6 → List Bool) (st : Tapes 2 q) (j : Fin 6) :
    (bank hs st).head (header j) = 1 ∧
    (bank hs st).tape (header j) = BinaryDescriptorStack.descriptor (hs j) := by
  fin_cases j <;> constructor <;> first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm

private theorem bank_frame (old hs : Fin 6 → List Bool) (st : Tapes 2 q) (i : Fin 40)
    (hi : ∀ j, i ≠ (header j).val) :
    (bank hs st).head i = (bank old st).head i ∧
    (bank hs st).tape i = (bank old st).tape i := by
  change Fin (38+2) at i
  induction i using Fin.addCases with
  | right i => simp only [bank,RecursiveChildHeaderHandoff.canonical,Tapes.append,Fin.addCases_right]; trivial
  | left i =>
    change Fin (13+25) at i
    induction i using Fin.addCases with
    | right i => simp only [bank,RecursiveChildHeaderHandoff.canonical,Tapes.append,Fin.addCases_left,Fin.addCases_right]; trivial
    | left i =>
      simp only [bank,RecursiveChildHeaderHandoff.canonical,Tapes.append,Fin.addCases_left] at *
      have h0 := hi 0; have h1 := hi 1; have h2 := hi 2
      have h3 := hi 3; have h4 := hi 4; have h5 := hi 5
      fin_cases i <;> simp_all [header,RecursiveDimensionBank.bank]

private theorem saved_congr (ops : List (Slot descriptorStack)) (xs : Fin 40 → List Bool)
    (v w : Tapes 40 q) (hh : v.head descriptorStack = w.head descriptorStack)
    (ht : v.tape descriptorStack = w.tape descriptorStack) :
    (saved descriptorStack ops xs v).head descriptorStack = (saved descriptorStack ops xs w).head descriptorStack ∧
    (saved descriptorStack ops xs v).tape descriptorStack = (saved descriptorStack ops xs w).tape descriptorStack := by
  induction ops generalizing v w with
  | nil => exact ⟨hh,ht⟩
  | cons op ops ih =>
    exact ih (write descriptorStack op xs v) (write descriptorStack op xs w)
      (by simp only [write,setTape,Function.update_self,hh])
      (by simp only [write,setTape,Function.update_self,hh,ht])

attribute [local irreducible] saved

/-- The still-pending return code, before it is physically popped. -/
def pending (st : Tapes 2 q) (code : FiniteReturnStack.Code k) : Tapes 2 q :=
  FiniteReturnStackAt.pushed 1 code st

private theorem bank_left_head (hs : Fin 6 → List Bool) (st : Tapes 2 q) (i : Fin 38) :
    (bank hs st).head (Fin.castAdd 2 i) = (RecursiveChildHeaderHandoff.canonical (q := q) hs).head i := by
  simp only [bank,Tapes.append,Fin.addCases_left]
private theorem bank_left_tape (hs : Fin 6 → List Bool) (st : Tapes 2 q) (i : Fin 38) :
    (bank hs st).tape (Fin.castAdd 2 i) = (RecursiveChildHeaderHandoff.canonical hs).tape i := by
  simp only [bank,Tapes.append,Fin.addCases_left]
private theorem bank_right_head (hs : Fin 6 → List Bool) (st : Tapes 2 q) (i : Fin 2) :
    (bank hs st).head (Fin.natAdd 38 i) = st.head i := by
  simp only [bank,Tapes.append,Fin.addCases_right]
private theorem bank_right_tape (hs : Fin 6 → List Bool) (st : Tapes 2 q) (i : Fin 2) :
    (bank hs st).tape (Fin.natAdd 38 i) = st.tape i := by
  simp only [bank,Tapes.append,Fin.addCases_right]
private theorem saved_head_projection (hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) (i : Fin 2) :
    (savedStacks hs st code).head i = (pushed hs st code).head (Fin.natAdd 38 i) := rfl
private theorem saved_tape_projection (hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) (i : Fin 2) :
    (savedStacks hs st code).tape i = (pushed hs st code).tape (Fin.natAdd 38 i) := rfl

private theorem saved_zero_head (old : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (savedStacks old st code).head 0 =
      (saved descriptorStack fields (words old) (bank old st)).head descriptorStack := by
  rw [saved_head_projection,show Fin.natAdd 38 (0 : Fin 2) = descriptorStack by rfl,pushed]
  exact (FiniteReturnStackAt.pushed_frame pcStack descriptorStack (by decide) code _).1
private theorem saved_one_head (old : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (savedStacks old st code).head 1 = st.head 1+k := by
  rw [saved_head_projection,show Fin.natAdd 38 (1 : Fin 2) = pcStack by rfl,pushed]
  have hf := saved_frame descriptorStack fields (words old) (bank old st) pcStack (by decide)
  simp only [FiniteReturnStackAt.pushed,setTape,Function.update_self,hf.1,hf.2]
  rfl
private theorem saved_zero_tape (old : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (savedStacks old st code).tape 0 =
      (saved descriptorStack fields (words old) (bank old st)).tape descriptorStack := by
  rw [saved_tape_projection,show Fin.natAdd 38 (0 : Fin 2) = descriptorStack by rfl,pushed]
  exact (FiniteReturnStackAt.pushed_frame pcStack descriptorStack (by decide) code _).2
private theorem saved_one_tape (old : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (savedStacks old st code).tape 1 = FiniteReturnStack.wordPart (st.tape 1) (st.head 1) code k le_rfl := by
  rw [saved_tape_projection,show Fin.natAdd 38 (1 : Fin 2) = pcStack by rfl,pushed]
  have hf := saved_frame descriptorStack fields (words old) (bank old st) pcStack (by decide)
  simp only [FiniteReturnStackAt.pushed,setTape,Function.update_self,hf.1,hf.2]
  rfl
private theorem tapes_append_ext (v : Tapes 40 q) (left : Tapes 38 q) (right : Tapes 2 q)
    (hl : ∀ i : Fin 38, v.head (Fin.castAdd 2 i) = left.head i ∧ v.tape (Fin.castAdd 2 i) = left.tape i)
    (h0 : v.head descriptorStack = right.head 0 ∧ v.tape descriptorStack = right.tape 0)
    (h1 : v.head pcStack = right.head 1 ∧ v.tape pcStack = right.tape 1) : v = left.append right := by
  have h (i : Fin 40) : v.head i = (left.append right).head i ∧ v.tape i = (left.append right).tape i := by
    change Fin (38+2) at i
    induction i using Fin.addCases with
    | left i => simpa only [Tapes.append,Fin.addCases_left] using hl i
    | right i =>
      fin_cases i
      · exact h0
      · exact h1
  cases v with
  | mk vh vt =>
    exact congrArg₂ Tapes.mk (funext fun i => (h i).1) (funext fun i => (h i).2)

private theorem saved_bank_left (old hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) (i : Fin 38) :
    (saved descriptorStack fields (words old) (bank hs (pending st code))).head (Fin.castAdd 2 i) =
      (RecursiveChildHeaderHandoff.canonical (q := q) hs).head i ∧
    (saved descriptorStack fields (words old) (bank hs (pending st code))).tape (Fin.castAdd 2 i) =
      (RecursiveChildHeaderHandoff.canonical hs).tape i := by
  have he : Fin.castAdd 2 i ≠ descriptorStack := by
    intro h; have h' := congrArg Fin.val h; simp [descriptorStack] at h'; omega
  have hf := saved_frame descriptorStack fields (words old) (bank hs (pending st code)) _ he
  exact ⟨hf.1.trans (bank_left_head hs (pending st code) i),hf.2.trans (bank_left_tape hs (pending st code) i)⟩

private theorem pending_zero (st : Tapes 2 q) (code : FiniteReturnStack.Code k) :
    (pending st code).head 0 = st.head 0 ∧ (pending st code).tape 0 = st.tape 0 :=
  FiniteReturnStackAt.pushed_frame 1 0 (by decide) code st

private theorem input_stack_equal (old hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (bank hs (pending st code)).head descriptorStack = (bank old st).head descriptorStack ∧
    (bank hs (pending st code)).tape descriptorStack = (bank old st).tape descriptorStack := by
  exact pending_zero st code

private theorem saved_pending_congr (old hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (saved descriptorStack fields (words old) (bank hs (pending st code))).head descriptorStack =
      (saved descriptorStack fields (words old) (bank old st)).head descriptorStack ∧
    (saved descriptorStack fields (words old) (bank hs (pending st code))).tape descriptorStack =
      (saved descriptorStack fields (words old) (bank old st)).tape descriptorStack :=
  saved_congr fields (words old) (bank hs (pending st code)) (bank old st)
    (input_stack_equal old hs st code).1 (input_stack_equal old hs st code).2

private theorem saved_bank_zero (old hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (saved descriptorStack fields (words old) (bank hs (pending st code))).head descriptorStack = (savedStacks old st code).head 0 ∧
    (saved descriptorStack fields (words old) (bank hs (pending st code))).tape descriptorStack = (savedStacks old st code).tape 0 := by
  rw [saved_zero_head old st code,saved_zero_tape old st code]
  exact saved_pending_congr old hs st code

private theorem saved_bank_one (old hs : Fin 6 → List Bool) (st : Tapes 2 q)
    (code : FiniteReturnStack.Code k) :
    (saved descriptorStack fields (words old) (bank hs (pending st code))).head pcStack = (savedStacks old st code).head 1 ∧
    (saved descriptorStack fields (words old) (bank hs (pending st code))).tape pcStack = (savedStacks old st code).tape 1 := by
  have hp := saved_frame descriptorStack fields (words old) (bank hs (pending st code)) pcStack (by decide)
  exact ⟨hp.1.trans (saved_one_head old st code).symm,hp.2.trans (saved_one_tape old st code).symm⟩

theorem saved_bank (old hs : Fin 6 → List Bool) (st : Tapes 2 q) (code : FiniteReturnStack.Code k) :
    saved descriptorStack fields (words old) (bank hs (pending st code)) = bank hs (savedStacks old st code) :=
  tapes_append_ext (saved descriptorStack fields (words old) (bank hs (pending st code)))
    (RecursiveChildHeaderHandoff.canonical hs) (savedStacks old st code)
    (saved_bank_left old hs st code) (saved_bank_zero old hs st code) (saved_bank_one old hs st code)

theorem restored_bank (old hs : Fin 6 → List Bool) (st : Tapes 2 q) :
    restored fields (words old) (bank hs st) = bank old st := by
  have he (i : Fin 40) :
      (restored fields (words old) (bank hs st)).head i = (bank old st).head i ∧
      (restored fields (words old) (bank hs st)).tape i = (bank old st).tape i := by
    by_cases hi : ∃ j, (header j).val = i
    · obtain ⟨j,rfl⟩ := hi
      have h := restored_field fields fields_nodup (words old) (bank hs st) (header j) ((mem_fields _).mpr ⟨j,rfl⟩)
      rw [words_header] at h
      have hh := header_bank old st j
      exact ⟨h.1.trans hh.1.symm,h.2.trans hh.2.symm⟩
    · have hn : ∀ j, i ≠ (header j).val := by simpa only [not_exists,ne_eq,eq_comm] using hi
      have h := restored_frame fields (words old) (bank hs st) i (by
        intro op hop; obtain ⟨j,rfl⟩ := (mem_fields op).mp hop; exact hn j)
      have hb := bank_frame old hs st i hn
      exact ⟨h.1.trans hb.1,h.2.trans hb.2⟩
  apply congrArg₂ Tapes.mk
  · funext i; exact (he i).1
  · funext i; exact (he i).2

noncomputable def program := BinaryDescriptorFrameRestore.program (a := q) descriptorStack fields

def cost (old hs : Fin 6 → List Bool) :=
  BinaryDescriptorCleanupList.cost (BinaryDescriptorFrameRestore.slots fields) (words hs)+1+
    BinaryDescriptorFrames.cost fields (words old)

/-- Actual child output is accepted with its occupied headers and both saved
stacks. Return restores the parent bank, retaining only the pending PC frame. -/
theorem restores (old hs : Fin 6 → List Bool) (st : Tapes 2 q) (code : FiniteReturnStack.Code k)
    (hd : RecursiveStackAllocation.Available 0 st) :
    HoareTime (program (q := q)) (fun w => w = bank hs (savedStacks old st code))
      (fun w => w = bank old (pending st code)) (cost old hs) := by
  have hf : BinaryDescriptorFrames.Free descriptorStack fields (words old) (bank hs (pending st code)) :=
    RecursiveStackAllocation.descriptor_free _ _ _ _ hd
  have hh := BinaryDescriptorFrameRestore.restore_hoare descriptorStack fields fields_nodup
    (words old) (words hs) (bank hs (pending st code)) (by
      intro op hop; obtain ⟨j,rfl⟩ := (mem_fields op).mp hop
      rw [words_header]; exact header_bank hs _ j) hf
  simpa only [saved_bank,restored_bank,program,cost] using hh

end IntegerMultBounds.Machine.RecursiveChildCallReturn
