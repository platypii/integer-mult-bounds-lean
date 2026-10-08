import IntegerMultBounds.Machine.RecursiveMixedInitialized
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Physically erase the generated XOR clock and volume descriptor after an
initialized same-view operation sequence. The controls start and end wholly
blank, while all role data, headers, scratch and auxiliary tapes are exact. -/
namespace IntegerMultBounds.Machine.RecursiveMixedClean
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveMixedSchedule (Op Data commonCount commonBank)
open RecursiveMixedInitialized (inputBank)
open SharedBankStageInput (raw)
variable {t u : ℕ}

def controlSlot (i : Fin 2) : Fin (commonCount t u) := Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd u i))
def cleanupSlots : List (Fin (commonCount t u)) := [controlSlot 0,controlSlot 1]

def cleanup : SharedBankSkeleton.Skeleton (commonCount t u) prime where
  tapes := commonCount t u
  states := _
  program := BinaryDescriptorCleanupList.program (by unfold commonCount; omega) cleanupSlots
  slots := id
  slots_injective := Function.injective_id

private theorem descriptor_binary (bs : List Bool) :
    BinaryDescriptorStack.descriptor (a := prime) bs = CountedLoopReuseAlphabet.binary bs := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded,← CountedLoopReuseAlphabet.encoding_binary]
  rfl

private theorem cleanup_nodup : (cleanupSlots (t := t) (u := u)).Nodup := by
  simp only [cleanupSlots,List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,or_false,not_false_eq_true,and_true]
  intro he
  have hv := congrArg Fin.val he
  simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero,Fin.val_one] at hv
  omega

private theorem control_header {v : Descriptor} (hs : Fin 6 → List Bool) (bs : List Bool)
    (aux : Tapes u prime) (data : Data t v) (i : Fin 2) :
    (commonBank hs bs aux data).head (controlSlot i) = 1 ∧
      (commonBank hs bs aux data).tape (controlSlot i) =
        BinaryDescriptorStack.descriptor (if i = 0 then [] else bs) := by
  rw [descriptor_binary]
  fin_cases i <;>
    simp only [controlSlot,commonBank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_right,Fin.addCases_left,
      RecursiveXorRoleBank.controls,CountedLoopReuseAlphabet.controls,Fin.zero_eta,Fin.isValue,↓reduceIte]
  · exact ⟨trivial,rfl⟩
  · exact ⟨rfl,rfl⟩

private theorem cleanup_result {v : Descriptor} (hs : Fin 6 → List Bool) (bs : List Bool)
    (aux : Tapes u prime) (data : Data t v) :
    BinaryDescriptorCleanupList.cleared cleanupSlots (commonBank hs bs aux data) = inputBank hs aux data := by
  have hc (i : Fin 2) := BinaryDescriptorCleanupList.cleared_slot cleanupSlots cleanup_nodup
    (commonBank hs bs aux data) (controlSlot i) (by fin_cases i <;> simp [cleanupSlots])
  have hf (i : Fin (commonCount t u)) (hi : i ∉ cleanupSlots) :=
    BinaryDescriptorCleanupList.cleared_frame cleanupSlots (commonBank hs bs aux data) i hi
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i =>
      have hn : Fin.castAdd (7+(2+u)) i ∉ cleanupSlots := by
        simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false]
        intro he
        rcases he with he | he <;> have hh := congrArg Fin.val he <;>
          simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero,Fin.val_one] at hh <;> omega
      first
        | simpa only [BinaryDescriptorCleanupList.cleared,cleanupSlots,SharedPlacementAlphabet.setTape,commonBank,inputBank,RecursiveVolumeRoleBank.bank,RecursiveShiftRoleBank.common,
            Tapes.append,Fin.addCases_left,Fin.addCases_right] using (hf _ hn).1
        | simpa only [BinaryDescriptorCleanupList.cleared,cleanupSlots,SharedPlacementAlphabet.setTape,commonBank,inputBank,RecursiveVolumeRoleBank.bank,RecursiveShiftRoleBank.common,
            Tapes.append,Fin.addCases_left,Fin.addCases_right] using (hf _ hn).2
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        have hn : Fin.natAdd t (Fin.castAdd (2+u) i) ∉ cleanupSlots := by
          simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false]
          intro he
          rcases he with he | he <;> have hh := congrArg Fin.val he <;>
            simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero,Fin.val_one] at hh <;> omega
        first
          | simpa only [BinaryDescriptorCleanupList.cleared,cleanupSlots,SharedPlacementAlphabet.setTape,commonBank,inputBank,RecursiveVolumeRoleBank.bank,RecursiveShiftRoleBank.common,
              Tapes.append,Fin.addCases_left,Fin.addCases_right] using (hf _ hn).1
          | simpa only [BinaryDescriptorCleanupList.cleared,cleanupSlots,SharedPlacementAlphabet.setTape,commonBank,inputBank,RecursiveVolumeRoleBank.bank,RecursiveShiftRoleBank.common,
              Tapes.append,Fin.addCases_left,Fin.addCases_right] using (hf _ hn).2
      | right i =>
        induction i using Fin.addCases with
        | left i => first
          | simpa only [controlSlot,BinaryDescriptorCleanupList.cleared,cleanupSlots,SharedPlacementAlphabet.setTape,inputBank,RecursiveVolumeRoleBank.bank,RecursiveShiftRoleBank.common,Tapes.append,
              Fin.addCases_left,Fin.addCases_right,RecursiveVolumeRoleBank.controls,SharedBank.empty] using (hc i).1
          | simpa only [controlSlot,BinaryDescriptorCleanupList.cleared,cleanupSlots,SharedPlacementAlphabet.setTape,inputBank,RecursiveVolumeRoleBank.bank,RecursiveShiftRoleBank.common,Tapes.append,
              Fin.addCases_left,Fin.addCases_right,RecursiveVolumeRoleBank.controls,SharedBank.empty] using (hc i).2
        | right i =>
          have hn : Fin.natAdd t (Fin.natAdd 7 (Fin.natAdd 2 i)) ∉ cleanupSlots := by
            simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false]
            intro he
            rcases he with he | he <;> have hh := congrArg Fin.val he <;>
              simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero,Fin.val_one] at hh <;> omega
          first
            | simpa only [BinaryDescriptorCleanupList.cleared,cleanupSlots,SharedPlacementAlphabet.setTape,commonBank,inputBank,RecursiveVolumeRoleBank.bank,RecursiveShiftRoleBank.common,
                Tapes.append,Fin.addCases_left,Fin.addCases_right] using (hf _ hn).1
            | simpa only [BinaryDescriptorCleanupList.cleared,cleanupSlots,SharedPlacementAlphabet.setTape,commonBank,inputBank,RecursiveVolumeRoleBank.bank,RecursiveShiftRoleBank.common,
                Tapes.append,Fin.addCases_left,Fin.addCases_right] using (hf _ hn).2

/-- Both sentinels, all volume bits and both head resets are physically paid. -/
theorem cleanup_hoare {v : Descriptor} (hs : Fin 6 → List Bool) (bs : List Bool)
    (aux : Tapes u prime) (data : Data t v) :
    HoareTime (cleanup (t := t) (u := u)).program
      (fun w => w = raw (commonBank hs bs aux data) (commonCount t u))
      (fun w => w = raw (inputBank hs aux data) (commonCount t u)) (2*bs.length+10) := by
  have hh := BinaryDescriptorCleanupList.cleanup_hoare (by unfold commonCount; omega : 0 < commonCount t u)
    cleanupSlots cleanup_nodup (fun i => if i = controlSlot 0 then [] else bs) (commonBank hs bs aux data) (by
      intro i hi
      simp only [cleanupSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl
      · simpa only [↓reduceIte] using control_header hs bs aux data 0
      · have hn : controlSlot (t := t) (u := u) 1 ≠ controlSlot 0 := by
          intro he; have hv := congrArg Fin.val he
          simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero,Fin.val_one] at hv
          omega
        simpa only [hn,show (1 : Fin 2) ≠ 0 by decide,↓reduceIte] using control_header hs bs aux data 1)
  rw [cleanup_result] at hh
  have hr (c : Tapes (commonCount t u) prime) : raw c (commonCount t u) = c := by
    apply congrArg₂ Tapes.mk <;> funext i <;> simp only [dite_eq_left i.isLt]
  rw [hr,hr]
  convert hh using 1 <;> first | rfl | skip
  simp only [BinaryDescriptorCleanupList.cost,cleanupSlots,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  have hn : controlSlot (t := t) (u := u) 1 ≠ controlSlot 0 := by
    intro he; have hv := congrArg Fin.val he
    simp only [controlSlot,Fin.val_natAdd,Fin.val_castAdd,Fin.val_zero,Fin.val_one] at hv
    omega
  simp only [hn,↓reduceIte,List.length_nil]
  omega

def machine (ops : List (Op t)) : SharedBankSkeleton.Skeleton (commonCount t u) prime :=
  SharedBankSkeleton.compose (RecursiveMixedInitialized.machine (u := u) ops) cleanup

def coefficient (ops : List (Op t)) := 51796+(ops.map RecursiveMixedSchedule.coefficient).sum+ops.length

/-- Only original payloads and six headers are inputs. Generated controls and
all other private tapes are blank again at the exact final bank. -/
theorem realizes {v : Descriptor} (ops : List (Op t)) (hs : Fin 6 → List Bool)
    (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (data : Data t v) :
    HoareTime (machine (u := u) ops).program
      (fun w => w = raw (inputBank hs aux data) (machine (u := u) ops).tapes)
      (fun w => w = raw (inputBank hs aux (RecursiveMixedSchedule.run ops data)) (machine (u := u) ops).tapes)
      (coefficient ops*volume prime v) := by
  have hh := SharedBankRawCompose.realizes (RecursiveMixedInitialized.machine (u := u) ops) cleanup
    (fun _ => rfl) (fun _ => rfl) _ _ _ _ _
    (RecursiveMixedInitialized.realizes_linear ops hs aux hv hp data)
    (cleanup_hoare hs (RecursiveVolumeConstruct.bits (q := prime) v) aux (RecursiveMixedSchedule.run ops data))
  apply hh.consequence (fun _ h => h) (fun _ h => h)
  have hlen := RecursiveVolumeClean.bits_length (q := prime) v
  have hV : 0 < volume prime v := by
    rcases hp with ⟨hA,hR,hB,hC,hE⟩
    have hq := Shared50ModularControl.prime_prime.pos
    unfold volume
    positivity
  unfold coefficient
  nlinarith

end
end IntegerMultBounds.Machine.RecursiveMixedClean
