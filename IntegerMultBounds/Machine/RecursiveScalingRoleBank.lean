import IntegerMultBounds.Machine.RecursiveShiftRoleBank
import IntegerMultBounds.Machine.RecursiveInterchangeScalingClean

/-! Concrete H/D scaling on exactly the shift adapter's permanent role/header
bank. The standalone machine depends only on the fixed coefficient, target,
and physical wire. Supplied runtime headers are read and preserved, not assumed
regrouped or synthesized for free. -/
namespace IntegerMultBounds.Machine.RecursiveScalingRoleBank
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveInterchangeScaling (Target)
open RecursiveInterchangeScalingConstruct (TapeCount sourceSlot destSlot headerSlot)
open RecursiveShiftRoleBank (common commonPorts commonPorts_injective headers source updated)
variable {t u : ℕ}

def ports (r : ℚ) : Fin 8 → Fin (TapeCount r+TapeCount r) :=
  fun i => Fin.castAdd (TapeCount r) (Fin.addCases (motive := fun _ => Fin (TapeCount r))
    (fun j : Fin 2 => if j = 0 then sourceSlot r else destSlot r) (headerSlot r) i)

private theorem ports_value (r : ℚ) (i : Fin 8) :
    (ports r i).val = if i = 0 then 16+(FlatAffineScaling.sourceSlot r).val
      else if i = 1 then 16+(ActualAffineScalingStream.destinationSlot r).val else i.val+1 := by
  fin_cases i <;> rfl

theorem ports_injective (r : ℚ) : Function.Injective (ports r) := by
  intro i j h
  have hv := congrArg Fin.val h
  rw [ports_value,ports_value] at hv
  have hne : (FlatAffineScaling.sourceSlot r).val ≠ (ActualAffineScalingStream.destinationSlot r).val :=
    fun h => FlatAffineScalingPayload.slots_distinct r (Fin.ext h)
  apply Fin.ext
  fin_cases i <;> fin_cases j <;> norm_num at hv <;> omega

def program {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r) (target : Target) (wire : Fin t) :=
  Placement.placed (RecursiveInterchangeScalingClean.program hr target)
    (CleanSubbank.placement (ports r) (commonPorts (u := u) wire) (commonPorts_injective wire))

private theorem pair_eq {N : ℕ} (a : Fin N → Fin 4) :
    FlatAffineScalingPayload.pair (radix := prime) a = FlatRepeatedControlArray.pair a := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

private theorem local_headers {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (target : Target) (j : Fin 6) :
    (RecursiveInterchangeScalingClean.bank (r := r) hs a target).head (ports r (Fin.natAdd 2 j)) = 1 ∧
    (RecursiveInterchangeScalingClean.bank (r := r) hs a target).tape (ports r (Fin.natAdd 2 j)) =
      RadixZeroFill.encodedBinary (hs j) := by
  simpa only [ports,Fin.addCases_right,RecursiveInterchangeScalingClean.bank,Tapes.append,Fin.addCases_left]
    using RecursiveInterchangeScalingConstruct.input_header (r := r) hs a target j

private theorem local_payload {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) (target : Target) :
    SharedBank.payload (RecursiveInterchangeScalingClean.bank (r := r) hs a target) (ports r) =
      (FlatRepeatedControlArray.pair a).append (headers hs) := by
  have h := (RecursiveInterchangeScalingClean.payload hr hs a target).trans (pair_eq a)
  apply congrArg₂ Tapes.mk
  · funext i
    change Fin (2+6) at i
    induction i using Fin.addCases with
    | left i =>
      have hi := congrFun (congrArg Tapes.head h) i
      fin_cases i <;> exact hi
    | right j => simpa only [SharedBank.payload,Tapes.append,Fin.addCases_right,headers]
        using (local_headers r hs a target j).1
  · funext i
    change Fin (2+6) at i
    induction i using Fin.addCases with
    | left i =>
      have hi := congrFun (congrArg Tapes.tape h) i
      fin_cases i <;> exact hi
    | right j => simpa only [SharedBank.payload,Tapes.append,Fin.addCases_right,headers]
        using (local_headers r hs a target j).2

private theorem selected_kept (r : ℚ) (i : Fin (TapeCount r))
    (hi : RecursiveInterchangeScalingClean.keep r i = true) :
    ∃ j, ports r j = Fin.castAdd (TapeCount r) i := by
  simp only [RecursiveInterchangeScalingClean.keep,RecursiveInterchangeScalingClean.right,
    Bool.or_eq_true,decide_eq_true_eq] at hi
  rcases hi with ⟨hlo,hhi⟩ | rfl | rfl
  · let j : Fin 6 := ⟨i.val-3,by omega⟩
    refine ⟨Fin.natAdd 2 j,?_⟩
    apply Fin.ext
    simp only [ports,Fin.addCases_right,Fin.val_castAdd,headerSlot,Fin.val_natAdd]
    dsimp only [j]
    omega
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩

private theorem local_clean {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (target : Target) :
    SharedBank.strip (RecursiveInterchangeScalingClean.bank (r := r) hs a target) (ports r) =
      SharedBank.empty (TapeCount r+TapeCount r) prime := by
  have hblank (i : Fin (TapeCount r+TapeCount r)) (hi : ¬∃ j, ports r j = i) :
      (RecursiveInterchangeScalingClean.bank (r := r) hs a target).head i = 0 ∧
      (RecursiveInterchangeScalingClean.bank (r := r) hs a target).tape i = fun _ => blank := by
    induction i using Fin.addCases with
    | left i =>
      exact RecursiveInterchangeScalingClean.private_blank hs a target i
        (Bool.eq_false_iff.mpr (fun hk => hi (selected_kept r i hk)))
    | right i => exact RecursiveInterchangeScalingClean.trackers_blank hs a target i
  apply congrArg₂ Tapes.mk
  · funext i
    by_cases hi : ∃ j, ports r j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).1
  · funext i
    by_cases hi : ∃ j, ports r j = i
    · simp only [hi,↓reduceIte]
    · simpa only [SharedBank.strip,hi,↓reduceIte,SharedBank.empty] using (hblank i hi).2

/-- The same fixed machine scales one chosen role for every positive runtime
layout, returning identical headers, spectators, auxiliaries, and blank workspace. -/
theorem realizes {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (target : Target) (wire : Fin t) (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (aux : Tapes u prime) (a : Fin (volume prime v) → Fin 4)
    (hh : roles.head wire = 0) (ht : roles.tape wire = source a)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    HoareTime (program (u := u) hr target wire)
      (fun x => x = CleanSubbank.bank (common roles hs aux))
      (fun x => x = CleanSubbank.bank
        (common (updated roles wire (RecursiveInterchangeScaling.array hr a target)) hs aux))
      (RecursiveInterchangeScalingClean.bound r (volume prime v)) := by
  apply CleanSubbank.realizes _ (ports r) (commonPorts wire) (ports_injective r) (commonPorts_injective wire)
    _ _ (RecursiveInterchangeScalingClean.bank (r := r) hs a target)
    (RecursiveInterchangeScalingClean.bank (r := r) hs (RecursiveInterchangeScaling.array hr a target) target) _
  · exact (local_payload hr hs a target).trans (RecursiveShiftRoleBank.common_payload roles wire hs aux a hh ht).symm
  · exact (local_payload hr hs _ target).trans (RecursiveShiftRoleBank.common_payload _ wire hs aux _
      (by simp [updated,SharedPlacementAlphabet.setTape])
      (by simp [updated,SharedPlacementAlphabet.setTape])).symm
  · exact local_clean r hs a target
  · exact local_clean r hs _ target
  · exact RecursiveShiftRoleBank.common_frame roles wire hs aux _
  · exact RecursiveInterchangeScalingClean.realizes_hoare hr hs a target hv hpos

theorem realizes_array {v : Descriptor} {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (target : Target) (wire : Fin t) (roles : Tapes t prime) (hs : Fin 6 → List Bool)
    (aux : Tapes u prime) (a : Fin (volume prime v) → Fin 4)
    (hh : roles.head wire = 0) (ht : roles.tape wire = source a)
    (hv : RecursiveDimensionBank.Headers v hs) (hpos : v.Positive) :
    HoareTime (program (u := u) hr target wire)
      (fun x => x = CleanSubbank.bank (common roles hs aux))
      (fun x => x = CleanSubbank.bank
          (common (updated roles wire (RecursiveInterchangeScaling.array hr a target)) hs aux) ∧
        ∀ z : RecursiveInterchangeScaling.Address v,
          RecursiveInterchangeScaling.array hr a target
            (RecursiveInterchangeScaling.index (RecursiveInterchangeScaling.scaleAddress r z target)) =
              a (RecursiveInterchangeScaling.index z))
      (RecursiveInterchangeScalingClean.bound r (volume prime v)) := by
  apply (realizes hr target wire roles hs aux a hh ht hv hpos).consequence (fun _ h => h) ?_ le_rfl
  intro x hx
  exact ⟨hx,RecursiveInterchangeScaling.array_entry hr a target⟩

end
end IntegerMultBounds.Machine.RecursiveScalingRoleBank
