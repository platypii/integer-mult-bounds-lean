import IntegerMultBounds.Machine.RecursiveInterchangeShiftConstruct
import IntegerMultBounds.Machine.CleanExecution

/-! A clean, reusable seven-factor H-controlled D shift. Only the original six
headers and common payload pair survive; every generated dimension, control,
arithmetic workspace and tracker is physically erased and reset. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeShiftClean
open RecursiveInterchangeLayout (Descriptor volume)
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeShiftConstruct (sourceSlot destSlot)
noncomputable section

/-- Header heads are one; all other original heads start at zero. -/
def right (i : Fin 34) : Bool := decide (3 ≤ i.val ∧ i.val < 9)
def keep (i : Fin 34) : Bool := right i || decide (i = sourceSlot ∨ i = destSlot)
def headerSlot (j : Fin 6) : Fin 34 := Fin.castAdd 21 (Fin.castAdd 4 (Fin.natAdd 3 j))

def bank {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :=
  (RecursiveInterchangeShiftConstruct.input hs a).append (SharedBank.empty 34 prime)

def program (r : ℚ) := CleanExecution.program (RecursiveInterchangeShiftConstruct.program r) right keep

private theorem input_head {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :
    (RecursiveInterchangeShiftConstruct.input hs a).head = TrackedInit.position right := by
  funext i
  fin_cases i <;> rfl

private theorem input_header {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4)
    (j : Fin 6) :
    (RecursiveInterchangeShiftConstruct.input hs a).head (headerSlot j) = 1 ∧
    (RecursiveInterchangeShiftConstruct.input hs a).tape (headerSlot j) = RadixZeroFill.encodedBinary (hs j) := by
  unfold RecursiveInterchangeShiftConstruct.input RecursiveShiftInitialize.input headerSlot
  simp only [Tapes.append,Fin.addCases_left]
  exact RecursiveDimensionBank.headers_preserved hs _ j

private theorem input_private {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4)
    (i : Fin 34) (hi : keep i = false) :
    (RecursiveInterchangeShiftConstruct.input hs a).head i = 0 ∧
    (RecursiveInterchangeShiftConstruct.input hs a).tape i = (fun _ => blank) := by
  change Fin (13+21) at i
  induction i using Fin.addCases with
  | left i =>
    apply RecursiveInterchangeShiftConstruct.input_dimension_blank hs a i
    simp only [keep,right,Bool.or_eq_false_iff,decide_eq_false_iff_not,Fin.val_castAdd] at hi
    omega
  | right i =>
    apply RecursiveInterchangeShiftConstruct.input_local_blank hs a i
    intro he
    subst i
    simp [keep,sourceSlot] at hi

private theorem kept_cases (i : Fin 34) (hi : keep i = true) :
    (∃ j : Fin 6, i = headerSlot j) ∨ i = sourceSlot ∨ i = destSlot := by
  simp only [keep,right,Bool.or_eq_true,decide_eq_true_eq] at hi
  rcases hi with ⟨hlo,hhi⟩ | hi
  · left
    refine ⟨⟨i.val-3,by omega⟩,?_⟩
    apply Fin.ext
    simp [headerSlot]
    omega
  · exact Or.inr hi

private theorem kept_eq {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (i : Fin 34) (hi : keep i = true) :
    (RecursiveInterchangeShiftConstruct.output r hs a).head i =
        (RecursiveInterchangeShiftConstruct.input hs (RecursiveInterchangeShift.array r a)).head i ∧
    (RecursiveInterchangeShiftConstruct.output r hs a).tape i =
        (RecursiveInterchangeShiftConstruct.input hs (RecursiveInterchangeShift.array r a)).tape i := by
  have hp := (RecursiveInterchangeShiftConstruct.output_payload r hs a).trans
    (RecursiveInterchangeShiftConstruct.input_payload hs (RecursiveInterchangeShift.array r a)).symm
  rcases kept_cases i hi with ⟨j,rfl⟩ | rfl | rfl
  · have ho := RecursiveInterchangeShiftConstruct.headers_preserved r hs a j
    have hi := input_header hs (RecursiveInterchangeShift.array r a) j
    exact ⟨ho.1.trans hi.1.symm,ho.2.trans hi.2.symm⟩
  · exact ⟨congrArg (fun w : Tapes 2 prime => w.head 0) hp,congrArg (fun w : Tapes 2 prime => w.tape 0) hp⟩
  · exact ⟨congrArg (fun w : Tapes 2 prime => w.head 1) hp,congrArg (fun w : Tapes 2 prime => w.tape 1) hp⟩

private theorem retained_eq {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :
    TrackedCleanupList.retained keep (RecursiveInterchangeShiftConstruct.output r hs a) =
      RecursiveInterchangeShiftConstruct.input hs (RecursiveInterchangeShift.array r a) := by
  apply congrArg₂ Tapes.mk
  · funext i
    cases hk : keep i with
    | true => exact (kept_eq r hs a i hk).1
    | false => simpa only [TrackedCleanupList.retained,hk,Bool.false_eq_true,ite_false,
        RecursiveInterchangeShiftConstruct.input,RecursiveShiftInitialize.input,Tapes.append]
        using (input_private hs (RecursiveInterchangeShift.array r a) i hk).1.symm
  · funext i
    cases hk : keep i with
    | true => exact (kept_eq r hs a i hk).2
    | false => simpa only [TrackedCleanupList.retained,hk,Bool.false_eq_true,ite_false,
        RecursiveInterchangeShiftConstruct.input,RecursiveShiftInitialize.input,Tapes.append]
        using (input_private hs (RecursiveInterchangeShift.array r a) i hk).2.symm

/-- Same canonical bank before and after execution, with no private leftovers. -/
theorem realizes_hoare {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program r) (fun w => w = bank hs a)
      (fun w => w = bank hs (RecursiveInterchangeShift.array r a))
      (221536*volume prime v+32370) := by
  have hh := CleanExecution.realizes (RecursiveInterchangeShiftConstruct.program r) right keep
    (RecursiveInterchangeShiftConstruct.input hs a) (RecursiveInterchangeShiftConstruct.output r hs a)
    (1288*volume prime v+186) (input_head hs a) (fun i hi => (input_private hs a i hi).2)
    (RecursiveInterchangeShiftConstruct.constructs_hoare r hs a hv hvpos)
  rw [retained_eq] at hh
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- All trackers are literal blank at head zero at every reusable boundary. -/
theorem trackers_blank {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (i : Fin 34) :
    (bank hs a).head (Fin.natAdd 34 i) = 0 ∧ (bank hs a).tape (Fin.natAdd 34 i) = (fun _ => blank) := by
  simp only [bank,Tapes.append,Fin.addCases_right,SharedBank.empty]
  trivial

/-- Every private original tape is likewise blank, including the erased metadata markers. -/
theorem private_blank {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4)
    (i : Fin 34) (hi : keep i = false) :
    (bank hs a).head (Fin.castAdd 34 i) = 0 ∧ (bank hs a).tape (Fin.castAdd 34 i) = (fun _ => blank) := by
  simpa only [bank,Tapes.append,Fin.addCases_left] using input_private hs a i hi

theorem payload {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :
    SharedPayload.payload (bank hs a) (Fin.castAdd 34 sourceSlot) (Fin.castAdd 34 destSlot) =
      FlatRepeatedControlArray.pair a := by
  simpa only [bank,SharedPayload.payload,Tapes.append,Fin.addCases_left] using
    RecursiveInterchangeShiftConstruct.input_payload hs a

/-- Fixed zero/one entry-head pattern, including all blank tracking heads. -/
theorem bank_head {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :
    (bank hs a).head = Fin.addCases (TrackedInit.position right) (fun _ => 0) := by
  unfold bank Tapes.append SharedBank.empty
  rw [input_head]

theorem realizes_array {v : Descriptor} (r : ℚ) (hden : r.den < prime) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program r) (fun w => w = bank hs a)
      (fun w => w = bank hs (RecursiveInterchangeShift.array r a) ∧
        SharedPayload.payload w (Fin.castAdd 34 sourceSlot) (Fin.castAdd 34 destSlot) =
          FlatRepeatedControlArray.pair (RecursiveInterchangeShift.array r a) ∧
        ∀ x : RecursiveInterchangeScaling.Address v,
          RecursiveInterchangeShift.array r a (RecursiveInterchangeScaling.index (RecursiveInterchangeShift.shiftAddress r x)) =
            a (RecursiveInterchangeScaling.index x) ∧
          (RecursiveInterchangeShift.shiftAddress r x).d.val =
            (x.d.val+(Swap.Modular.ratMod (ActualAffineScaling.modulus v.width) r*
              (x.h.val : ZMod (ActualAffineScaling.modulus v.width))).val)%ActualAffineScaling.modulus v.width)
      (221536*volume prime v+32370) := by
  apply (realizes_hoare r hs a hv hvpos).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact ⟨rfl,payload hs _,fun x =>
    ⟨RecursiveInterchangeShift.array_entry r a x,RecursiveInterchangeShift.shiftAddress_d r hden x⟩⟩


end
end IntegerMultBounds.Machine.RecursiveInterchangeShiftClean
