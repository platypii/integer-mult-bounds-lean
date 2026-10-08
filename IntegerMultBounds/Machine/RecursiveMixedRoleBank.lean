import IntegerMultBounds.Machine.RecursiveMixedClean
import IntegerMultBounds.Machine.RecursiveViewFrameRoleBank

/-! Place an initialized, fully cleaned mixed block on the same permanent
role/header/stack bank as recursive scalar segments. Its two transient controls
are private; the dedicated stack and arbitrary auxiliaries are framed literally. -/
namespace IntegerMultBounds.Machine.RecursiveMixedRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveMixedSchedule (Op Data commonCount)
open RecursiveViewFrameRoleBank (count bank)
open SharedBankStageInput (raw)
variable {t u : ℕ}

/-- Permanent portion used by a nonrecursive gate, excluding the caller stack. -/
def base (roles : Tapes t prime) (hs : Fin 6 → List Bool) : Tapes (t+7) prime :=
  roles.append ((SharedBank.empty 1 prime).append (RecursiveShiftRoleBank.headers hs))

private theorem raw_raw {k n N : ℕ} (c : Tapes k prime) (hkn : k ≤ n) : raw (raw c n) N = raw c N := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    by_cases hi : i.val < k
    · have hn : i.val < n := lt_of_lt_of_le hi hkn
      simp only [raw,hn,hi,↓reduceDIte]
    · by_cases hn : i.val < n <;> simp only [raw,hn,hi,↓reduceDIte]

private theorem input_raw {v : Descriptor} (hs : Fin 6 → List Bool) (data : Data t v) :
    RecursiveMixedInitialized.inputBank hs (SharedBank.empty 0 prime) data =
      raw (base (RecursiveRoleSerialization.roles data) hs) (commonCount t 0) := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i =>
      have hi : (Fin.castAdd (7+(2+0)) i).val < t+7 := by simp only [Fin.val_castAdd]; omega
      simp only [hi,↓reduceDIte]
      first
      | change _ = (base (RecursiveRoleSerialization.roles data) hs).head (Fin.castAdd 7 i)
      | change _ = (base (RecursiveRoleSerialization.roles data) hs).tape (Fin.castAdd 7 i)
      all_goals simp only [base,Tapes.append,Fin.addCases_left]
    | right i =>
      induction i using Fin.addCases with
      | left i =>
        have hi : (Fin.natAdd t (Fin.castAdd (2+0) i)).val < t+7 := by
          simp only [Fin.val_natAdd,Fin.val_castAdd]; omega
        simp only [hi,↓reduceDIte]
        first
        | change _ = (base (RecursiveRoleSerialization.roles data) hs).head (Fin.natAdd t i)
        | change _ = (base (RecursiveRoleSerialization.roles data) hs).tape (Fin.natAdd t i)
        all_goals simp only [base,Tapes.append,Fin.addCases_left,Fin.addCases_right]
      | right i =>
        have hi : ¬(Fin.natAdd t (Fin.natAdd 7 i)).val < t+7 := by simp only [Fin.val_natAdd]; omega
        simp only [hi,↓reduceDIte,Tapes.append,Fin.addCases_right,RecursiveVolumeRoleBank.controls]
        induction i using Fin.addCases with
        | left i => simp only [Fin.addCases_left,SharedBank.empty]
        | right i => exact Fin.elim0 i

def localPorts (ops : List (Op t)) (i : Fin (t+7)) : Fin (RecursiveMixedClean.machine (u := 0) ops).tapes :=
  (RecursiveMixedClean.machine (u := 0) ops).slots ⟨i.val,by have := i.isLt; unfold commonCount; omega⟩

def commonPorts (i : Fin (t+7)) : Fin (count t u) := ⟨i.val,by have := i.isLt; unfold count; omega⟩

theorem localPorts_val (ops : List (Op t)) (i : Fin (t+7)) : (localPorts ops i).val = i.val := rfl

theorem localPorts_injective (ops : List (Op t)) : Function.Injective (localPorts ops) := by
  intro i j he
  have hv := congrArg Fin.val he
  exact Fin.ext hv

theorem commonPorts_injective : Function.Injective (commonPorts (t := t) (u := u)) := by
  intro i j he
  have hv := congrArg Fin.val he
  exact Fin.ext hv

private theorem common_payload (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (st : Tapes 1 prime) (aux : Tapes u prime) :
    SharedBank.payload (bank roles hs st aux) commonPorts = base roles hs := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i =>
      have he : commonPorts (u := u) (Fin.castAdd 7 i) = Fin.castAdd (7+(1+u)) i := rfl
      simp only [he,bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left]
    | right i =>
      have he : commonPorts (u := u) (Fin.natAdd t i) = Fin.natAdd t (Fin.castAdd (1+u) i) := rfl
      simp only [he,bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_left,Fin.addCases_right]

private theorem common_frame (roles roles' : Tapes t prime) (hs : Fin 6 → List Bool)
    (st : Tapes 1 prime) (aux : Tapes u prime) :
    SharedBank.strip (bank roles hs st aux) commonPorts = SharedBank.strip (bank roles' hs st aux) commonPorts := by
  have sel (i : Fin (count t u)) (hi : i.val < t+7) : ∃ j, commonPorts (u := u) j = i :=
    ⟨⟨i.val,hi⟩,Fin.ext rfl⟩
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals
    induction i using Fin.addCases with
    | left i =>
      have hi : (Fin.castAdd (7+(1+u)) i).val < t+7 := by simp only [Fin.val_castAdd]; omega
      simp only [sel _ hi,↓reduceIte]
    | right i => simp only [bank,RecursiveShiftRoleBank.common,Tapes.append,Fin.addCases_right]

def program (ops : List (Op t)) := Placement.placed (RecursiveMixedClean.machine (u := 0) ops).program
  (CleanSubbank.placement (localPorts ops) (commonPorts (t := t) (u := u)) commonPorts_injective)

def machine (ops : List (Op t)) : SharedBankSkeleton.Skeleton (count t u) prime where
  tapes := count t u+(RecursiveMixedClean.machine (u := 0) ops).tapes
  states := _
  program := program ops
  slots := Fin.castAdd _
  slots_injective := Fin.castAdd_injective _ _

/-- No XOR control or private header is supplied. The exact original stack,
auxiliaries and six headers survive, and every private tape is blank afterward. -/
theorem realizes {v : Descriptor} (ops : List (Op t)) (hs : Fin 6 → List Bool)
    (st : Tapes 1 prime) (aux : Tapes u prime) (hv : RecursiveDimensionBank.Headers v hs)
    (hp : v.Positive) (data : Data t v) :
    HoareTime (machine (u := u) ops).program
      (fun w => w = raw (bank (RecursiveRoleSerialization.roles data) hs st aux) (machine (u := u) ops).tapes)
      (fun w => w = raw (bank (RecursiveRoleSerialization.roles (RecursiveMixedSchedule.run ops data)) hs st aux)
        (machine (u := u) ops).tapes)
      (RecursiveMixedClean.coefficient ops*volume prime v) := by
  have hh := RecursiveMixedClean.realizes ops hs (SharedBank.empty 0 prime) hv hp data
  rw [input_raw,input_raw,raw_raw _ (by omega),raw_raw _ (by omega)] at hh
  have hl := CleanSubbank.realizes (RecursiveMixedClean.machine (u := 0) ops).program
    (localPorts ops) commonPorts (localPorts_injective ops) commonPorts_injective
    (bank (RecursiveRoleSerialization.roles data) hs st aux)
    (bank (RecursiveRoleSerialization.roles (RecursiveMixedSchedule.run ops data)) hs st aux)
    _ _ _
    ((SharedBankRawCompose.payload_raw _ _ (localPorts_val ops)).trans (common_payload _ _ _ _).symm)
    ((SharedBankRawCompose.payload_raw _ _ (localPorts_val ops)).trans (common_payload _ _ _ _).symm)
    (SharedBankRawCompose.strip_raw _ _ (localPorts_val ops))
    (SharedBankRawCompose.strip_raw _ _ (localPorts_val ops))
    (common_frame _ _ _ _ _) hh
  simpa only [machine,program,SharedBankRawCompose.bank_eq_raw] using hl

end
end IntegerMultBounds.Machine.RecursiveMixedRoleBank
