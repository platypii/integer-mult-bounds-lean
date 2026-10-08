import IntegerMultBounds.Machine.RecursiveViewFrame
import IntegerMultBounds.Machine.RecursiveViewRoleBank
import IntegerMultBounds.Machine.SharedBankRawCompose

/-! Save and restore six headers on the permanent role bank. The first auxiliary
tape is the dedicated descriptor stack; all remaining auxiliaries are exact
spectators. Both adapters leave all seven private placement tapes blank. -/
namespace IntegerMultBounds.Machine.RecursiveViewFrameRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
variable {t u : ℕ}

abbrev count (t u : ℕ) := t+(7+(1+u))

def bank (roles : Tapes t prime) (hs : Fin 6 → List Bool) (st : Tapes 1 prime) (aux : Tapes u prime) :=
  RecursiveShiftRoleBank.common roles hs (st.append aux)

def commonPorts : Fin 7 → Fin (count t u) :=
  fun i => Fin.addCases (motive := fun _ => Fin (count t u))
    (fun j : Fin 6 => Fin.natAdd t (Fin.castAdd (1+u) (Fin.natAdd 1 j)))
    (fun _ : Fin 1 => Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd u 0))) i

private theorem ports_value (i : Fin 7) :
    (commonPorts (t := t) (u := u) i).val = if i.val < 6 then t+1+i.val else t+7 := by
  fin_cases i <;> simp [commonPorts,Fin.addCases]

theorem commonPorts_injective : Function.Injective (commonPorts (t := t) (u := u)) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [ports_value,ports_value] at hv
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  split_ifs at hv <;> omega

def pushProgram := Placement.placed (RecursiveViewFrame.pushProgram (q := prime))
  (CleanSubbank.placement (id : Fin 7 → Fin 7) (commonPorts (t := t) (u := u)) commonPorts_injective)
def restoreProgram := Placement.placed (RecursiveViewFrame.restoreProgram (q := prime))
  (CleanSubbank.placement (id : Fin 7 → Fin 7) (commonPorts (t := t) (u := u)) commonPorts_injective)

private theorem payload (roles : Tapes t prime) (hs : Fin 6 → List Bool) (st : Tapes 1 prime) (aux : Tapes u prime) :
    SharedBank.payload (bank roles hs st aux) commonPorts = RecursiveViewFrame.bank hs st := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    change Fin (6+1) at i
    induction i using Fin.addCases with
    | left i => simp only [bank,commonPorts,RecursiveShiftRoleBank.common,
        RecursiveShiftRoleBank.headers,Tapes.append,Fin.addCases_left,Fin.addCases_right]
    | right i => fin_cases i; simp only [bank,commonPorts,RecursiveShiftRoleBank.common,
        RecursiveShiftRoleBank.headers,Tapes.append,Fin.addCases_left,Fin.addCases_right]; rfl

private theorem frame (roles : Tapes t prime) (hs ch : Fin 6 → List Bool)
    (st st' : Tapes 1 prime) (aux : Tapes u prime) :
    SharedBank.strip (bank roles hs st aux) commonPorts = SharedBank.strip (bank roles ch st' aux) commonPorts := by
  have selH (j : Fin 6) : ∃ i, commonPorts (t := t) (u := u) i =
      Fin.natAdd t (Fin.castAdd (1+u) (Fin.natAdd 1 j)) :=
    ⟨Fin.castAdd 1 j,by simp only [commonPorts,Fin.addCases_left]⟩
  have selS (j : Fin 1) : ∃ i, commonPorts (t := t) (u := u) i =
      Fin.natAdd t (Fin.natAdd 7 (Fin.castAdd u j)) := by
    fin_cases j
    exact ⟨6,rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i => simp only [bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left]
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        change Fin (1+6) at i
        induction i using Fin.addCases with
        | left i => simp only [bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left,Fin.addCases_right]
        | right i => simp only [selH i,↓reduceIte]
      | right i =>
        induction i using Fin.addCases with
        | left i => simp only [selS i,↓reduceIte]
        | right i => simp only [bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_right]

theorem push_hoare (roles : Tapes t prime) (hs : Fin 6 → List Bool) (st : Tapes 1 prime) (aux : Tapes u prime) :
    HoareTime (pushProgram (t := t) (u := u))
      (fun w => w = CleanSubbank.bank (bank roles hs st aux))
      (fun w => w = CleanSubbank.bank (bank roles hs (RecursiveViewFrame.savedStack hs st) aux))
      (RecursiveViewFrame.pushCost hs) := by
  apply CleanSubbank.realizes _ id commonPorts Function.injective_id commonPorts_injective
    _ _ (RecursiveViewFrame.bank hs st) (RecursiveViewFrame.bank hs (RecursiveViewFrame.savedStack hs st)) _
  · exact (SharedBankFrames.payload_identity _).trans (payload roles hs st aux).symm
  · exact (SharedBankFrames.payload_identity _).trans (payload roles hs _ aux).symm
  · exact SharedBankFrames.strip_identity _
  · exact SharedBankFrames.strip_identity _
  · exact frame roles hs hs st _ aux
  · exact RecursiveViewFrame.push_hoare hs st

theorem restore_hoare (roles : Tapes t prime) (old hs : Fin 6 → List Bool) (st : Tapes 1 prime) (aux : Tapes u prime)
    (hf : RecursiveViewFrame.Free old st) :
    HoareTime (restoreProgram (t := t) (u := u))
      (fun w => w = CleanSubbank.bank (bank roles hs (RecursiveViewFrame.savedStack old st) aux))
      (fun w => w = CleanSubbank.bank (bank roles old st aux)) (RecursiveViewFrame.restoreCost old hs) := by
  apply CleanSubbank.realizes _ id commonPorts Function.injective_id commonPorts_injective
    _ _ (RecursiveViewFrame.bank hs (RecursiveViewFrame.savedStack old st)) (RecursiveViewFrame.bank old st) _
  · exact (SharedBankFrames.payload_identity _).trans (payload roles hs _ aux).symm
  · exact (SharedBankFrames.payload_identity _).trans (payload roles old st aux).symm
  · exact SharedBankFrames.strip_identity _
  · exact SharedBankFrames.strip_identity _
  · exact frame roles hs old _ st aux
  · exact RecursiveViewFrame.restore_hoare old hs st hf

def pushSkeleton : SharedBankSkeleton.Skeleton (count t u) prime where
  tapes := count t u+7
  states := _
  program := pushProgram
  slots := Fin.castAdd 7
  slots_injective := Fin.castAdd_injective _ _

def restoreSkeleton : SharedBankSkeleton.Skeleton (count t u) prime where
  tapes := count t u+7
  states := _
  program := restoreProgram
  slots := Fin.castAdd 7
  slots_injective := Fin.castAdd_injective _ _

end
end IntegerMultBounds.Machine.RecursiveViewFrameRoleBank
