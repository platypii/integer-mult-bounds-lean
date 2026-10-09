import IntegerMultBounds.Machine.ActivePrefixStageNativeRows
import IntegerMultBounds.Machine.ActivePrefixStagePairData

/-! Physical source/target header replacement for canonical native rows.
The literal native source stays unchanged when coordinate pairs change. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageNativePairData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageNativeRows (Rows core bank flat)
open ActivePrefixStagePairData (changePair pairWords)
open ActivePrefixStageSlotRewrite (updated)
open SharedPlacementAlphabet (setTape)
open Networks.Shared50ModularControl (prime)
open Networks.BinaryRowProgram (Op)
open RecursiveChildQuotientsConstant (bits)
variable {s : Shape} {B : ℕ}

abbrev count := ActivePrefixStageNative.tapes
abbrev public_le := ActivePrefixStageNativeCore.public_le

def focus (i : Fin 2) : Fin count := Fin.castLE public_le (if i=0 then 11 else 12)

theorem focus_injective : Function.Injective focus := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd (congrArg Fin.val h) (by decide)

private theorem updated_native (i : Fin 66) (hi : i≠65) (n : ℕ)
    (v : Tapes 66 prime) (f : ℤ → Fin (prime+4)) :
    updated i n (setTape v 65 f 0)=setTape (updated i n v) 65 f 0 := by
  unfold updated setTape
  congr 1 <;> exact (Function.update_comm hi _ _ _).symm

theorem core_pair (d : Inputs s) (op : Op (Fin d.stage.slots)) (xs : Rows d B) :
    updated (12:Fin 66) op.target.val (updated (11:Fin 66) op.source.val (core d xs))=
      core (changePair d op) xs := by
  rw [←ActivePrefixStageNativeRows.core_from_raw d (fun _ => false) xs,
    updated_native _ (by decide),updated_native _ (by decide),
    ActivePrefixStagePairData.original_pair]
  exact ActivePrefixStageNativeRows.core_from_raw _ _ _

theorem bank_pair (d : Inputs s) (op : Op (Fin d.stage.slots)) (xs : Rows d B) :
    updated (focus 1) op.target.val (updated (focus 0) op.source.val (bank d xs))=
      bank (changePair d op) xs := by
  unfold bank updated
  rw [show focus 0=Fin.castLE public_le (11:Fin 66) from rfl,
    show focus 1=Fin.castLE public_le (12:Fin 66) from rfl,
    ←ActivePrefixEarlySequenceOriginalPlaced.raw_set public_le,
    ←ActivePrefixEarlySequenceOriginalPlaced.raw_set public_le]
  exact congrArg (fun v => SharedBankStageInput.raw v count) (core_pair d op xs)

theorem headers (d : Inputs s) (xs : Rows d B) (i : Fin 2) :
    (bank d xs).head (focus i)=1 ∧
    (bank d xs).tape (focus i)=BinaryDescriptorStack.descriptor (pairWords d i) := by
  have hh := ActivePrefixStageFullEndpoint.original_header d (fun _ => false) (if i=0 then 11 else 12)
  unfold bank
  rw [←ActivePrefixStageNativeRows.core_from_raw d (fun _ => false) xs]
  fin_cases i
  all_goals
    simpa [focus,SharedBankStageInput.raw,setTape,pairWords,
      ActivePrefixStageHeadersData.originalValues,
      BinaryDescriptorStackRoundtrip.descriptor_encoded] using hh

def program {M : ℕ} (op : Op (Fin M)) := ActivePrefixStageSlotRewrite.pair
  (a:=prime) (focus 0) (focus 1) op.source.val op.target.val

abbrev cost (d : Inputs s) (op : Op (Fin d.stage.slots)) := ActivePrefixStagePairData.cost d op

theorem runs (d : Inputs s) (op : Op (Fin d.stage.slots)) (xs : Rows d B) :
    HoareTime (program op) (fun w => w=bank d xs) (fun w => w=bank (changePair d op) xs)
      (cost d op) := by
  have h0 := headers d xs 0
  have h1 := headers d xs 1
  have h := ActivePrefixStageSlotRewrite.pair_runs (focus 0) (focus 1)
    (fun h => by have := focus_injective h; contradiction) op.source.val op.target.val (bank d xs)
    (bits d.stage.source.val) (bits d.stage.target.val) h0.2 h0.1 h1.2 h1.1
  rw [bank_pair] at h
  exact h

end
end IntegerMultBounds.Machine.ActivePrefixStageNativePairData
