import IntegerMultBounds.Machine.SliceHeaderPlacement
import IntegerMultBounds.Machine.ArbitraryWidthSchedule

/-! One actual arbitrary-offset power-width call. The machine constructs and
installs slice headers, runs the fixed recursive root program, restores the old
headers, and halts with exactly the selected-window permutation of the I/O word. -/
namespace IntegerMultBounds.Machine.ArbitrarySliceCall
noncomputable section
open Networks
open Shared50ModularControl (prime)
open Shared50NodeSegments (payloadCount)
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50RecursiveCallReady (Ready)
open Shared50RecursiveNodeSemantics (encoded)
open Shared50RecursiveNodeLayout (wires)
open RecursiveRoleSerialization (roles)
open SharedBankStageInput (raw)
attribute [local irreducible] Shared50PieceSchedule.pieces Shared50FixedControl.control
  Shared50RecursiveCallLayout.parked Shared50RecursiveBudget.base Shared50RecursiveBudget.node

abbrev rootCount := Shared50RecursiveRoot.tapeCount
abbrev commonCount := Shared50RecursiveImplementation.commonCount
abbrev tapeCount := rootCount+12

private theorem common_le : commonCount ≤ rootCount :=
  SharedBankFamily.common_le_tapeCount
    (Shared50RecursiveControl.block Shared50RecursiveImplementation.returnCapacity
      Shared50RecursiveImplementation.width Shared50RecursiveImplementation.pcStack
      (Shared50RecursiveImplementation.implementation Shared50RecursiveImplementation.returnWidth))

private def commonHeader (i : Fin 6) : Fin commonCount := RecursiveCallBank.headerSlot i

def headerSlot (i : Fin 6) : Fin rootCount := Fin.castLE common_le (commonHeader i)

private theorem header_injective : Function.Injective headerSlot := by
  intro i j he
  have hv := congrArg Fin.val he
  simp only [headerSlot,commonHeader,RecursiveCallBank.headerSlot,Fin.val_castLE,Fin.val_natAdd,Fin.val_castAdd] at hv
  apply Fin.ext
  omega

private theorem root_six_le : 6 ≤ rootCount := by
  have h := common_le
  change payloadCount+(7+((3+(1+(1+0)))+2)) ≤ rootCount at h
  omega

def headerPlacement := SliceHeaderPlacement.placement headerSlot header_injective root_six_le

def rootBank (data : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) : Tapes rootCount prime :=
  raw (Shared50RecursiveBank.bank data hs f p node scalar (SharedBank.empty 0 prime) st) rootCount

/-- Original root tape bank plus offset,width,nine clean work tapes,and one
separate slice-header stack. Every payload/root stack may carry its usual data. -/
def bank (data : Tapes payloadCount prime) (hs : Fin 6 → List Bool) (ts bs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (frame : Tapes 1 prime) : Tapes tapeCount prime :=
  (rootBank data hs f p node scalar st).append (SliceHeaderPlacement.tail ts bs frame)

private theorem common_header (data : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (i : Fin 6) :
    (Shared50RecursiveBank.bank data hs f p node scalar (SharedBank.empty 0 prime) st).head (commonHeader i) = 1 ∧
    (Shared50RecursiveBank.bank data hs f p node scalar (SharedBank.empty 0 prime) st).tape (commonHeader i) =
      RadixZeroFill.encodedBinary (hs i) := by
  simp only [Shared50RecursiveBank.bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,commonHeader,
    RecursiveCallBank.headerSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right,RecursiveShiftRoleBank.headers]
  constructor <;> first | rfl | trivial

private theorem root_header (data : Tapes payloadCount prime) (hs : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (i : Fin 6) :
    (rootBank data hs f p node scalar st).head (headerSlot i) = 1 ∧
    (rootBank data hs f p node scalar st).tape (headerSlot i) = RadixZeroFill.encodedBinary (hs i) := by
  simpa only [rootBank,raw,headerSlot,Fin.val_castLE,dite_eq_left (commonHeader i).isLt] using
    common_header data hs f p node scalar st i

private theorem common_frame (data : Tapes payloadCount prime) (hs hs' : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (i : Fin commonCount) (hn : ∀ j, commonHeader j ≠ i) :
    (Shared50RecursiveBank.bank data hs f p node scalar (SharedBank.empty 0 prime) st).head i =
      (Shared50RecursiveBank.bank data hs' f p node scalar (SharedBank.empty 0 prime) st).head i ∧
    (Shared50RecursiveBank.bank data hs f p node scalar (SharedBank.empty 0 prime) st).tape i =
      (Shared50RecursiveBank.bank data hs' f p node scalar (SharedBank.empty 0 prime) st).tape i := by
  change Fin (payloadCount+(7+7)) at i
  induction i using Fin.addCases with
  | left i =>
      simp only [Shared50RecursiveBank.bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,
        Tapes.append,Fin.addCases_left]
      constructor <;> first | rfl | trivial
  | right i =>
    induction i using Fin.addCases with
    | right i =>
      simp only [Shared50RecursiveBank.bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,
        Tapes.append,Fin.addCases_right]
      constructor <;> first | rfl | trivial
    | left i =>
      change Fin (1+6) at i
      induction i using Fin.addCases with
      | left i =>
        simp only [Shared50RecursiveBank.bank,RecursiveCallBank.bank,RecursiveShiftRoleBank.common,
          Tapes.append,Fin.addCases_left,Fin.addCases_right]
        constructor <;> first | rfl | trivial
      | right i => exact (hn i rfl).elim

private theorem root_frame (data : Tapes payloadCount prime) (hs hs' : Fin 6 → List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (i : Fin rootCount) (hn : ∀ j, headerSlot j ≠ i) :
    (rootBank data hs f p node scalar st).head i = (rootBank data hs' f p node scalar st).head i ∧
    (rootBank data hs f p node scalar st).tape i = (rootBank data hs' f p node scalar st).tape i := by
  by_cases hi : i.val < commonCount
  · have hh := common_frame data hs hs' f p node scalar st ⟨i.val,hi⟩ (by
      intro j hj
      apply hn j
      have hv := congrArg (fun x : Fin commonCount => x.val) hj
      exact Fin.ext hv)
    simpa only [rootBank,raw,dite_eq_left hi] using hh
  · simp only [rootBank,raw,dite_eq_right hi]
    constructor <;> first | rfl | trivial

private theorem header_active (data : Tapes payloadCount prime) (hs : Fin 6 → List Bool) (ts bs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (frame : Tapes 1 prime) :
    Placement.active headerPlacement (bank data hs ts bs f p node scalar st frame) =
      ArbitrarySliceHeaders.canonical hs ts bs frame :=
  SliceHeaderPlacement.active_bank headerSlot header_injective root_six_le _ hs ts bs frame
    (root_header data hs f p node scalar st)

private theorem header_extra (data : Tapes payloadCount prime) (hs hs' : Fin 6 → List Bool) (ts bs : List Bool)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime) (frame frame' : Tapes 1 prime) :
    Placement.extra headerPlacement (bank data hs ts bs f p node scalar st frame) =
      Placement.extra headerPlacement (bank data hs' ts bs f p node scalar st frame') :=
  SliceHeaderPlacement.extra_bank headerSlot header_injective root_six_le _ _ _ _
    (root_frame data hs hs' f p node scalar st)

private theorem placed_exact {s u t r cost : ℕ} {M : Program s r prime}
    (e : Fin (s+u) ≃ Fin t) (v w : Tapes t prime) (small small' : Tapes s prime)
    (ha : Placement.active e v = small) (hf : Placement.active e w = small')
    (he : Placement.extra e v = Placement.extra e w)
    (hh : HoareTime M (fun x => x = small) (fun x => x = small') cost) :
    HoareTime (Placement.placed M e) (fun x => x = v) (fun x => x = w) cost := by
  apply (Placement.hoare_at hh e v ha).consequence (fun _ h => h) _ le_rfl
  rintro x ⟨y,rfl,rfl⟩
  rw [Placement.replace,he,← hf]
  exact Placement.view _ _

def prepareProgram := Placement.placed (ArbitrarySliceHeaders.prepareProgram Shared50ModularControl.prime_prime.two_le) headerPlacement
def restoreProgram := Placement.placed (ArbitrarySliceHeaders.restoreProgram (q := prime)) headerPlacement

/-- The same fixed program handles every valid runtime offset and power width. -/
def program := seq (seq prepareProgram (extend Shared50RecursiveImplementation.program 12)) restoreProgram

def data {v : Descriptor} (x : Fin (volume prime v) → ZMod 2) : Tapes payloadCount prime :=
  roles (RecursiveRowsSerialization.sourceData wires (encoded x))

private theorem root_slice (depth : ℕ) (v : Descriptor) (t b : ℕ) (hfit : t+b ≤ v.width)
    (shape : Shared50RecursiveDepth.Shape depth (ArbitraryWidthPieces.slice prime v t b))
    (hs : Fin 6 → List Bool) (hv : RecursiveDimensionBank.Headers (ArbitraryWidthPieces.slice prime v t b) hs)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (x : Fin (volume prime v) → ZMod 2) :
    HoareTime Shared50RecursiveImplementation.program
      (fun z => z = rootBank (data x) hs f p node scalar st)
      (fun z => z = rootBank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs f p node scalar st)
      (Shared50RecursiveRootExecution.rootBudget depth (volume prime v)) := by
  have h := Shared50RecursiveRootExecution.root_budget_hoare _ shape hs hv f p node scalar st ready
    (ArbitraryWidthSliceTranspose.toSlice t b hfit x)
  have hin : data (ArbitraryWidthSliceTranspose.toSlice t b hfit x) = data x := by
    unfold data
    rw [Shared50RecursiveCallReady.source_roles,Shared50RecursiveCallReady.source_roles]
    exact congrArg Shared50RecursiveCallSemantics.childRoles
      (ArbitraryWidthSliceTranspose.toSlice_source t b hfit (encoded x))
  have hout : data (Shared50RecursiveNodeRows.transpose (one_dvd _)
      (ArbitraryWidthSliceTranspose.toSlice t b hfit x)) = data (ArbitraryWidthSliceTranspose.array t b hfit x) := by
    unfold data
    rw [Shared50RecursiveCallReady.source_roles,Shared50RecursiveCallReady.source_roles]
    exact congrArg Shared50RecursiveCallSemantics.childRoles
      (ArbitraryWidthSliceTranspose.return_source t b hfit (encoded x))
  change HoareTime _ (fun z => z = rootBank (data (ArbitraryWidthSliceTranspose.toSlice t b hfit x)) hs f p node scalar st)
    (fun z => z = rootBank (data (Shared50RecursiveNodeRows.transpose (one_dvd _)
      (ArbitraryWidthSliceTranspose.toSlice t b hfit x))) hs f p node scalar st) _ at h
  rw [hin,hout,ArbitraryWidthPieces.slice_volume prime v t b hfit] at h
  exact h

/-- Actual selected-window execution, with construction and occupied-header
restoration included. There is no supplied child trace or installed-header premise. -/
theorem call_hoare (depth : ℕ) (v : Descriptor) (hs : Fin 6 → List Bool) (ts bs : List Bool) (t b : ℕ)
    (hp : v.Positive) (hv : RecursiveDimensionBank.Headers v hs)
    (ht : Counter.value ts = t) (hb : Counter.value bs = b)
    (ct : GrowingCounterData.Canonical ts) (cb : GrowingCounterData.Canonical bs)
    (hfit : t+b ≤ v.width) (hw : b = 125000^depth)
    (hr : Shared50TapeGlobal.roleCount^depth ∣ v.rows)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime) (st : Tapes 2 prime)
    (ready : Ready f p node scalar st) (frame : Tapes 1 prime) (hfree : RecursiveViewFrame.Free hs frame)
    (x : Fin (volume prime v) → ZMod 2) :
    HoareTime program (fun z => z = bank (data x) hs ts bs f p node scalar st frame)
      (fun z => z = bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs ts bs f p node scalar st frame)
      (Shared50RecursiveRootExecution.rootBudget depth (volume prime v)+1030*volume prime v) := by
  let child := ArbitrarySliceDimensions.headers (q := prime) hs bs v t b
  let saved := RecursiveViewFrame.savedStack hs frame
  have hc : RecursiveDimensionBank.Headers (ArbitraryWidthPieces.slice prime v t b) child :=
    ArbitrarySliceDimensions.headers_valid hs bs v t b hv hb cb
  have hshape : Shared50RecursiveDepth.Shape depth (ArbitraryWidthPieces.slice prime v t b) :=
    ⟨ArbitraryWidthPieces.slice_positive _ Shared50ModularControl.prime_prime.pos v hp t b,hw,hr⟩
  have hprep : HoareTime prepareProgram
      (fun z => z = bank (data x) hs ts bs f p node scalar st frame)
      (fun z => z = bank (data x) child ts bs f p node scalar st saved) (900*volume prime v) :=
    placed_exact headerPlacement _ _ _ _ (header_active _ _ _ _ _ _ _ _ _ _) (header_active _ _ _ _ _ _ _ _ _ _)
      (header_extra _ _ _ _ _ _ _ _ _ _ _ _)
      (ArbitrarySliceHeaders.prepares Shared50ModularControl.prime_prime.two_le hs ts bs v t b frame hv hp ht hb ct cb hfit)
  have hroot := hoare_extend_eq (root_slice depth v t b hfit hshape child hc f p node scalar st ready x)
    (SliceHeaderPlacement.tail ts bs saved)
  have hrestore : HoareTime restoreProgram
      (fun z => z = bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) child ts bs f p node scalar st saved)
      (fun z => z = bank (data (ArbitraryWidthSliceTranspose.array t b hfit x)) hs ts bs f p node scalar st frame)
      (128*volume prime v) :=
    placed_exact headerPlacement _ _ _ _ (header_active _ _ _ _ _ _ _ _ _ _) (header_active _ _ _ _ _ _ _ _ _ _)
      (header_extra _ _ _ _ _ _ _ _ _ _ _ _)
      (ArbitrarySliceHeaders.restores Shared50ModularControl.prime_prime.two_le hs ts bs v t b frame hv hp hb cb hfit hfree)
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le v hp
  exact ((hprep.seq hroot).seq hrestore).consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.ArbitrarySliceCall
