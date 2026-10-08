import IntegerMultBounds.Machine.Shared50RecursiveImplementation
import IntegerMultBounds.Machine.Shared50RecursiveBankReturn

/-! Paid root frame creation agrees exactly with the recursive call frame. -/
namespace IntegerMultBounds.Machine.Shared50RecursiveRoot
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50RecursiveImplementation
open Shared50RecursiveBank (bank)
open BinaryDescriptorFrames
open SharedPlacementAlphabet (setTape)
open Shared50NodeSegments (payloadCount)
open SharedBankStageInput (raw)

private theorem saved_congr {t s a : ℕ} (x : Fin t) (y : Fin s)
    (ops : List (Slot x)) (other : List (Slot y)) (xs : Fin t → List Bool) (ys : Fin s → List Bool)
    (hm : ops.map (fun i : Slot x => xs i) = other.map (fun i : Slot y => ys i))
    (v : Tapes t a) (w : Tapes s a) (hh : v.head x = w.head y) (ht : v.tape x = w.tape y) :
    (saved x ops xs v).head x = (saved y other ys w).head y ∧
    (saved x ops xs v).tape x = (saved y other ys w).tape y := by
  induction ops generalizing other v w with
  | nil => cases other with
    | nil => exact ⟨hh,ht⟩
    | cons i is => simp at hm
  | cons i is ih =>
    cases other with
    | nil => simp at hm
    | cons j js =>
      have he := List.cons.inj hm
      apply ih js he.2 (write x i xs v) (write y j ys w)
      · simp only [write,setTape,Function.update_self,hh,he.1]
      · simp only [write,setTape,Function.update_self,hh,ht,he.1]

def words (hs : Fin 6 → List Bool) (i : Fin commonCount) : List Bool :=
  if h : payloadCount+1 ≤ i.val ∧ i.val < payloadCount+7 then
    hs ⟨i.val-(payloadCount+1),by omega⟩ else []

@[simp] theorem words_header (hs : Fin 6 → List Bool) (i : Fin 6) :
    words hs (headerField i) = hs i := by
  have hi := i.isLt
  have hh : payloadCount+1 ≤ (headerField i).val.val ∧ (headerField i).val.val < payloadCount+7 := by
    simp only [headerField,RecursiveCallBank.headerSlot,Fin.val_natAdd,Fin.val_castAdd]
    omega
  unfold words
  rw [dite_eq_left hh]
  apply congrArg hs
  apply Fin.ext
  simp only [headerField,RecursiveCallBank.headerSlot,Fin.val_natAdd,Fin.val_castAdd]
  omega

theorem same_words (hs : Fin 6 → List Bool) :
    rootFields.map (fun i : Slot descriptorStack => words hs i) =
      RecursiveChildCallSetup.fields.map (fun i : Slot RecursiveChildCallSetup.descriptorStack => RecursiveChildCallSetup.words hs i) := by
  simp only [rootFields,RecursiveChildCallSetup.fields,List.map_ofFn,Function.comp_def,words_header,
    RecursiveChildCallSetup.words_header]

def pushed (hs : Fin 6 → List Bool) (v : Tapes commonCount prime) :=
  FiniteReturnStackAt.pushed pcStack (Shared50RecursiveControl.rootCode returnCapacity)
    (saved descriptorStack rootFields (words hs) v)

private theorem stack_ne : descriptorStack ≠ pcStack := by
  intro h
  have he := congrArg Fin.val h
  simp only [descriptorStack,pcStack,Shared50RecursiveBank.returnSlot,Fin.val_natAdd] at he
  omega

private theorem local_stack_ne : RecursiveChildCallSetup.descriptorStack ≠ RecursiveChildCallSetup.pcStack := by decide

private theorem root_stack (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (i : Fin 2) :
    (bank roles hs f p node scalar (SharedBank.empty 0 prime) st).head (Shared50RecursiveBank.returnSlot i) = st.head i ∧
    (bank roles hs f p node scalar (SharedBank.empty 0 prime) st).tape (Shared50RecursiveBank.returnSlot i) = st.tape i := by
  simp only [bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,Shared50RecursiveBank.returnSlot,
    Tapes.append,Fin.addCases_right]
  trivial

private theorem local_stack (hs : Fin 6 → List Bool) (st : Tapes 2 prime) (i : Fin 2) :
    (RecursiveChildCallSetup.bank hs st).head (Fin.natAdd 38 i) = st.head i ∧
    (RecursiveChildCallSetup.bank hs st).tape (Fin.natAdd 38 i) = st.tape i := by
  simp only [RecursiveChildCallSetup.bank,Tapes.append,Fin.addCases_right]
  trivial

attribute [local irreducible] rootFields RecursiveChildCallSetup.fields saved

private theorem saved_projection (hs : Fin 6 → List Bool) (st : Tapes 2 prime) (i : Fin 2) :
    (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)).head i =
      (RecursiveChildCallSetup.pushed hs st (Shared50RecursiveControl.rootCode returnCapacity)).head (Fin.natAdd 38 i) ∧
    (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)).tape i =
      (RecursiveChildCallSetup.pushed hs st (Shared50RecursiveControl.rootCode returnCapacity)).tape (Fin.natAdd 38 i) := ⟨rfl,rfl⟩

/-- Both stack projections coincide with the existing child-call frame. -/
theorem pushed_stacks (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (i : Fin 2) :
    (pushed hs (bank roles hs f p node scalar (SharedBank.empty 0 prime) st)).head (Shared50RecursiveBank.returnSlot i) =
      (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)).head i ∧
    (pushed hs (bank roles hs f p node scalar (SharedBank.empty 0 prime) st)).tape (Shared50RecursiveBank.returnSlot i) =
      (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)).tape i := by
  let v := bank roles hs f p node scalar (SharedBank.empty 0 prime) st
  let w := RecursiveChildCallSetup.bank hs st
  have hs0 := root_stack roles hs f p node scalar st 0
  have ht0 := local_stack hs st 0
  have he := saved_congr descriptorStack RecursiveChildCallSetup.descriptorStack rootFields
    RecursiveChildCallSetup.fields (words hs) (RecursiveChildCallSetup.words hs) (same_words hs) v w
    (hs0.1.trans ht0.1.symm) (hs0.2.trans ht0.2.symm)
  have hf := saved_frame descriptorStack rootFields (words hs) v pcStack stack_ne.symm
  have hg := saved_frame RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields
    (RecursiveChildCallSetup.words hs) w RecursiveChildCallSetup.pcStack local_stack_ne.symm
  rw [(saved_projection hs st i).1,(saved_projection hs st i).2]
  fin_cases i
  · change (FiniteReturnStackAt.pushed pcStack _ _).head descriptorStack = _ ∧
      (FiniteReturnStackAt.pushed pcStack _ _).tape descriptorStack = _
    have hp := FiniteReturnStackAt.pushed_frame pcStack descriptorStack stack_ne
      (Shared50RecursiveControl.rootCode returnCapacity) (saved descriptorStack rootFields (words hs) v)
    have hq := FiniteReturnStackAt.pushed_frame RecursiveChildCallSetup.pcStack RecursiveChildCallSetup.descriptorStack local_stack_ne
      (Shared50RecursiveControl.rootCode returnCapacity)
      (saved RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields (RecursiveChildCallSetup.words hs) w)
    exact ⟨hp.1.trans (he.1.trans hq.1.symm),hp.2.trans (he.2.trans hq.2.symm)⟩
  · have hs1 := root_stack roles hs f p node scalar st 1
    have ht1 := local_stack hs st 1
    have hhpc : (saved descriptorStack rootFields (words hs) v).head pcStack =
        (saved RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields (RecursiveChildCallSetup.words hs) w).head RecursiveChildCallSetup.pcStack :=
      hf.1.trans (hs1.1.trans (ht1.1.symm.trans hg.1.symm))
    have htpc : (saved descriptorStack rootFields (words hs) v).tape pcStack =
        (saved RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields (RecursiveChildCallSetup.words hs) w).tape RecursiveChildCallSetup.pcStack :=
      hf.2.trans (hs1.2.trans (ht1.2.symm.trans hg.2.symm))
    change (FiniteReturnStackAt.pushed pcStack _ (saved descriptorStack rootFields (words hs) v)).head pcStack =
      (FiniteReturnStackAt.pushed RecursiveChildCallSetup.pcStack _
        (saved RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields (RecursiveChildCallSetup.words hs) w)).head RecursiveChildCallSetup.pcStack ∧
      (FiniteReturnStackAt.pushed pcStack _ (saved descriptorStack rootFields (words hs) v)).tape pcStack =
      (FiniteReturnStackAt.pushed RecursiveChildCallSetup.pcStack _
        (saved RecursiveChildCallSetup.descriptorStack RecursiveChildCallSetup.fields (RecursiveChildCallSetup.words hs) w)).tape RecursiveChildCallSetup.pcStack
    simp only [FiniteReturnStackAt.pushed,setTape,Function.update_self,hhpc,htpc]
    trivial



private theorem bank_spectators (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st st' : Tapes 2 prime)
    (i : Fin commonCount) (hd : i ≠ descriptorStack) (hp : i ≠ pcStack) :
    (bank roles hs f p node scalar (SharedBank.empty 0 prime) st).head i =
      (bank roles hs f p node scalar (SharedBank.empty 0 prime) st').head i ∧
    (bank roles hs f p node scalar (SharedBank.empty 0 prime) st).tape i =
      (bank roles hs f p node scalar (SharedBank.empty 0 prime) st').tape i := by
  change Fin (payloadCount+(7+((3+(1+(1+0)))+2))) at i
  induction i using Fin.addCases with
  | left i => simp only [bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left]; trivial
  | right i =>
    induction i using Fin.addCases with
    | left i => simp only [bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left,Fin.addCases_right]; trivial
    | right i =>
      induction i using Fin.addCases with
      | left i => simp only [bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left,Fin.addCases_right]; trivial
      | right i => fin_cases i
                   · exact False.elim (hd rfl)
                   · exact False.elim (hp rfl)

/-- Root saving is literally the same permanent-bank frame consumed by the
shared recursive restoration and decoded PC pop. -/
theorem pushed_bank (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    pushed hs (bank roles hs f p node scalar (SharedBank.empty 0 prime) st) =
      bank roles hs f p node scalar (SharedBank.empty 0 prime)
        (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)) := by
  have h (i : Fin commonCount) :
      (pushed hs (bank roles hs f p node scalar (SharedBank.empty 0 prime) st)).head i =
        (bank roles hs f p node scalar (SharedBank.empty 0 prime)
          (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity))).head i ∧
      (pushed hs (bank roles hs f p node scalar (SharedBank.empty 0 prime) st)).tape i =
        (bank roles hs f p node scalar (SharedBank.empty 0 prime)
          (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity))).tape i := by
    by_cases hd : i = descriptorStack
    · subst i
      have he := pushed_stacks roles hs f p node scalar st 0
      have ho := root_stack roles hs f p node scalar
        (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)) 0
      exact ⟨he.1.trans ho.1.symm,he.2.trans ho.2.symm⟩
    by_cases hp : i = pcStack
    · subst i
      have he := pushed_stacks roles hs f p node scalar st 1
      have ho := root_stack roles hs f p node scalar
        (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)) 1
      exact ⟨he.1.trans ho.1.symm,he.2.trans ho.2.symm⟩
    have he := RecursiveFrameControl.call_frame descriptorStack rootFields pcStack i hd hp
      (Shared50RecursiveControl.rootCode returnCapacity) (words hs)
      (bank roles hs f p node scalar (SharedBank.empty 0 prime) st)
    have ho := bank_spectators roles hs f p node scalar st
      (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)) i hd hp
    exact ⟨he.1.trans ho.1,he.2.trans ho.2⟩
  apply congrArg₂ Tapes.mk
  · funext i; exact (h i).1
  · funext i; exact (h i).2


abbrev tapeCount := Shared50RecursiveControl.tapeCount returnCapacity width pcStack (implementation returnWidth)

def setup := SharedBankFamily.padProgram
  (RecursiveFrameControl.callProgram (a := prime) descriptorStack rootFields pcStack
    (Shared50RecursiveControl.rootCode returnCapacity))
  (SharedBankFamily.common_le_tapeCount (Shared50RecursiveControl.block returnCapacity width pcStack (implementation returnWidth)))

private theorem header_bank (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (i : Fin 6) :
    (bank roles hs f p node scalar (SharedBank.empty 0 prime) st).head (headerField i) = 1 ∧
    (bank roles hs f p node scalar (SharedBank.empty 0 prime) st).tape (headerField i) =
      BinaryDescriptorStack.descriptor (hs i) := by
  simp only [bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,headerField,
    RecursiveCallBank.headerSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,RecursiveShiftRoleBank.headers]
  exact ⟨True.intro,(BinaryDescriptorStackRoundtrip.descriptor_encoded _).symm⟩

private theorem headers (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    ∀ i ∈ rootFields, (bank roles hs f p node scalar (SharedBank.empty 0 prime) st).head i = 1 ∧
      (bank roles hs f p node scalar (SharedBank.empty 0 prime) st).tape i =
        BinaryDescriptorStack.descriptor (words hs i) := by
  intro i hi
  rw [rootFields] at hi
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
  rw [words_header]
  exact header_bank roles hs f p node scalar st j

/-- Real, padded root setup; the bound includes its sequence join and PC push. -/
theorem setup_hoare (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) :
    HoareTime setup
      (fun w => w = raw (bank roles hs f p node scalar (SharedBank.empty 0 prime) st) tapeCount)
      (fun w => w = raw (bank roles hs f p node scalar (SharedBank.empty 0 prime)
        (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity))) tapeCount)
      (cost rootFields (words hs)+1+returnWidth) := by
  have h := RecursiveFrameControl.call_hoare descriptorStack rootFields pcStack
    (Shared50RecursiveControl.rootCode returnCapacity) (words hs)
    (bank roles hs f p node scalar (SharedBank.empty 0 prime) st) (headers roles hs f p node scalar st)
  change HoareTime _ _ (fun w => w = pushed hs (bank roles hs f p node scalar (SharedBank.empty 0 prime) st)) _ at h
  rw [pushed_bank] at h
  have hr (v : Tapes commonCount prime) : raw v commonCount = v := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp only [dite_eq_left i.isLt]
  apply SharedBankFamily.pad_realizes _ (le_refl commonCount) _ _ _
  simpa only [hr] using h

/-- The only remaining premise is execution of the concrete recursive graph
from its now-established physical saved-root bank. -/
theorem root_hoare (roles : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (post : TapePred tapeCount prime) (B : ℕ)
    (body : HoareTime graph
      (fun w => w = raw (bank roles hs f p node scalar (SharedBank.empty 0 prime)
        (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity))) tapeCount) post B) :
    HoareTime Shared50RecursiveImplementation.program
      (fun w => w = raw (bank roles hs f p node scalar (SharedBank.empty 0 prime) st) tapeCount)
      post (cost rootFields (words hs)+1+returnWidth+1+B) :=
  (setup_hoare roles hs f p node scalar st).seq body

theorem setup_cost_linear (v : RecursiveInterchangeLayout.Descriptor) (hp : v.Positive)
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers v hs) :
    cost rootFields (words hs)+1+returnWidth ≤
      (73+returnWidth)*RecursiveInterchangeLayout.volume prime v := by
  have hc := six_field_cost rootFields (by rw [rootFields,List.length_ofFn]) (words hs)
    (2*RecursiveInterchangeLayout.volume prime v) (by
      intro i hi
      rw [rootFields] at hi
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      rw [words_header]
      exact RecursiveRowsNode.header_length v hp hs hv j)
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  nlinarith

/-- A single blank suffix invariant suffices for arbitrarily nested frames. -/
theorem saved_available (hs : Fin 6 → List Bool) (st : Tapes 2 prime)
    (hd : RecursiveStackAllocation.Available 0 st) (hp : RecursiveStackAllocation.Available 1 st) :
    RecursiveStackAllocation.Available 0
      (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)) ∧
    RecursiveStackAllocation.Available 1
      (RecursiveChildCallSetup.savedStacks hs st (Shared50RecursiveControl.rootCode returnCapacity)) :=
  RecursiveStackAllocation.saved_stacks_available hs st _ hd hp

end
end IntegerMultBounds.Machine.Shared50RecursiveRoot
