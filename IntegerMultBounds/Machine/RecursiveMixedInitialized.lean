import IntegerMultBounds.Machine.RecursiveVolumeRoleBank
import IntegerMultBounds.Machine.RecursiveMixedSchedule
import IntegerMultBounds.Machine.SharedBankRawCompose

/-! One fixed mixed-operation machine starting from roles, six canonical headers,
and blank work. Its clock and full stream-volume descriptor are physically
constructed before any operation. Construction, all joins and complete private
cleanup are included in the linear time bound. As in RecursiveMixedSchedule,
all operations use the same supplied coordinate view; header regrouping and
recursive calls remain separate obligations. -/
namespace IntegerMultBounds.Machine.RecursiveMixedInitialized
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveMixedSchedule (Op Data commonCount commonBank)
open SharedBankStageInput (raw)
variable {t u : ℕ}

def prepare : SharedBankSkeleton.Skeleton (commonCount t u) prime where
  tapes := commonCount t u+34
  states := _
  program := RecursiveVolumeRoleBank.program (t := t) (u := u)
  slots := Fin.castAdd 34
  slots_injective := Fin.castAdd_injective _ _

def machine (ops : List (Op t)) : SharedBankSkeleton.Skeleton (commonCount t u) prime :=
  SharedBankSkeleton.compose (prepare (t := t) (u := u)) (RecursiveMixedSchedule.machine (u := u) ops)

def inputBank {v : Descriptor} (hs : Fin 6 → List Bool) (aux : Tapes u prime) (data : Data t v) :=
  RecursiveVolumeRoleBank.bank (RecursiveRoleSerialization.roles data) hs none aux

private theorem mixed_slots (ops : List (Op t)) (i : Fin (commonCount t u)) :
    ((RecursiveMixedSchedule.machine (u := u) ops).slots i).val = i.val := by
  cases ops <;> rfl

/-- Exact full contract: the caller supplies only canonical layout headers and
role payloads; both XOR controls and every private tape start blank. -/
theorem realizes {v : Descriptor} (ops : List (Op t)) (hs : Fin 6 → List Bool)
    (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (data : Data t v) :
    HoareTime (machine (u := u) ops).program
      (fun w => w = raw (inputBank hs aux data) (machine (u := u) ops).tapes)
      (fun w => w = raw (commonBank hs (RecursiveVolumeConstruct.bits (q := prime) v) aux (RecursiveMixedSchedule.run ops data))
        (machine (u := u) ops).tapes)
      (RecursiveVolumeClean.bound (volume prime v)+
        ((ops.map (RecursiveMixedSchedule.cost v (RecursiveVolumeConstruct.bits (q := prime) v))).sum+ops.length)+1) := by
  have hi := RecursiveVolumeRoleBank.realizes v (RecursiveRoleSerialization.roles data) hs aux hv hp
  simp only [SharedBankRawCompose.bank_eq_raw] at hi
  have ho := RecursiveMixedSchedule.realizes ops hs (RecursiveVolumeConstruct.bits (q := prime) v) aux hv hp
    (RecursiveVolumeConstruct.bits_value v) data
  exact SharedBankRawCompose.realizes (prepare (t := t) (u := u)) (RecursiveMixedSchedule.machine (u := u) ops)
    (fun _ => rfl) (mixed_slots ops) _ _ _ _ _ hi ho

/-- A fixed coefficient pays the entire initialized finite sequence. -/
theorem realizes_linear {v : Descriptor} (ops : List (Op t)) (hs : Fin 6 → List Bool)
    (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs) (hp : v.Positive) (data : Data t v) :
    HoareTime (machine (u := u) ops).program
      (fun w => w = raw (inputBank hs aux data) (machine (u := u) ops).tapes)
      (fun w => w = raw (commonBank hs (RecursiveVolumeConstruct.bits (q := prime) v) aux (RecursiveMixedSchedule.run ops data))
        (machine (u := u) ops).tapes)
      ((51783+(ops.map RecursiveMixedSchedule.coefficient).sum+ops.length)*volume prime v) := by
  have hq : 0 < prime := lt_trans (by decide : 0 < 2) Shared50ModularControl.prime_odd
  have hV : 0 < volume prime v := by
    rcases hp with ⟨hA,hR,hB,hC,hE⟩
    unfold volume
    positivity
  have hc := RecursiveVolumeClean.bound_linear (volume prime v) hV
  have hm := RecursiveMixedSchedule.total_cost_le (RecursiveVolumeConstruct.bits (q := prime) v) ops hV
    (RecursiveVolumeClean.bits_length v)
  exact (realizes ops hs aux hv hp data).consequence (fun _ h => h) (fun _ h => h) (by nlinarith)

end
end IntegerMultBounds.Machine.RecursiveMixedInitialized
