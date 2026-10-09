import IntegerMultBounds.Machine.BinaryPackedRowCount
import IntegerMultBounds.Machine.FixedHeaderBankCopy

/-! Shared original P/G/B/w headers, with a physically generated packed fiber
count in one of nine private tapes. Every other private tape is clean. -/
namespace IntegerMultBounds.Machine.BinaryPackedRowCountPlaced
noncomputable section
variable {t a : ℕ}
open SharedPlacementAlphabet (setTape)

def input (caller : Tapes t a) := caller.append (FixedHeaderBankCopy.empty 9)
def rowSlot : Fin (t+9) := Fin.natAdd t 0

def slot (focus : Fin 4 → Fin t) : Fin 13 → Fin (t+9) :=
  Fin.addCases (m := 4) (n := 9) (fun i => Fin.castAdd 9 (focus i)) (Fin.natAdd t)

theorem slot_injective (focus : Fin 4 → Fin t) (hf : Function.Injective focus) :
    Function.Injective (slot focus) := by
  intro i j he
  induction i using (Fin.addCases (m := 4) (n := 9)) with
  | left i =>
    induction j using (Fin.addCases (m := 4) (n := 9)) with
    | left j =>
      simp only [slot,Fin.addCases_left] at he
      have hh : focus i=focus j := Fin.castAdd_injective _ _ he
      exact congrArg (Fin.castAdd 9) (hf hh)
    | right j =>
      simp only [slot,Fin.addCases_left,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      change (focus i).val=t+j.val at hh
      have hi := (focus i).isLt
      omega
  | right i =>
    induction j using (Fin.addCases (m := 4) (n := 9)) with
    | left j =>
      simp only [slot,Fin.addCases_left,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      change t+i.val=(focus j).val at hh
      have hj := (focus j).isLt
      omega
    | right j =>
      simp only [slot,Fin.addCases_right] at he
      have hh := congrArg Fin.val he
      change t+i.val=t+j.val at hh
      exact congrArg (Fin.natAdd 4) (Fin.ext (by omega))

theorem size (focus : Fin 4 → Fin t) (hf : Function.Injective focus) : 13+(t-4)=t+9 := by
  have h := Fintype.card_le_of_injective focus hf
  simp only [Fintype.card_fin] at h
  omega

def placement (focus : Fin 4 → Fin t) (hf : Function.Injective focus) : Fin (13+(t-4)) ≃ Fin (t+9) :=
  InjectivePlacement.placement (slot focus) (slot_injective focus hf) (size focus hf)

theorem placement_active (focus : Fin 4 → Fin t) (hf : Function.Injective focus) (i : Fin 13) :
    placement focus hf (Fin.castAdd (t-4) i)=slot focus i := InjectivePlacement.active_slot _ _ _ _

def program (focus : Fin 4 → Fin t) (hf : Function.Injective focus) (a : ℕ) :=
  Placement.placed (BinaryPackedRowCount.program (a := a)) (placement focus hf)

def output (caller : Tapes t a) (P w G : ℕ) :=
  setTape (input caller) rowSlot (RadixZeroFill.encodedBinary (BinaryPackedRowCount.rowBits P w G)) 1

theorem active_input (caller : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 4 → List Bool)
    (ht : ∀ i, caller.tape (focus i)=RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i)=1) :
    Placement.active (placement focus hf) (input caller)=BinaryPackedRowCount.input hs := by
  unfold placement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> simp [input,slot,Tapes.append,Fin.addCases,FixedHeaderBankCopy.empty,
      RecursiveDimensionBank.head,hh]
  · funext i
    fin_cases i <;> simp [input,slot,Tapes.append,Fin.addCases,FixedHeaderBankCopy.empty,
      RecursiveDimensionBank.tape,ht]

private theorem native_output (hs : Fin 4 → List Bool) (P w G : ℕ) :
    BinaryPackedRowCount.output (a := a) hs P w G =
      setTape (BinaryPackedRowCount.input hs) 4
        (RadixZeroFill.encodedBinary (BinaryPackedRowCount.rowBits P w G)) 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- The only new retained tape contains the derived count. Every original
header and arbitrary complementary tape is framed. -/
theorem constructs (caller : Tapes t a) (focus : Fin 4 → Fin t) (hf : Function.Injective focus)
    (hs : Fin 4 → List Bool) (P w G : ℕ) (hG : 0 < G)
    (ht : ∀ i, caller.tape (focus i)=RadixZeroFill.encodedBinary (hs i))
    (hh : ∀ i, caller.head (focus i)=1)
    (hP : Counter.value (hs 0)=P) (hGv : Counter.value (hs 1)=G) (hw : Counter.value (hs 3)=w)
    (cP : GrowingCounterData.Canonical (hs 0)) (cG : GrowingCounterData.Canonical (hs 1))
    (cw : GrowingCounterData.Canonical (hs 3)) :
    HoareTime (program focus hf a) (fun z => z=input caller) (fun z => z=output caller P w G)
      (FixedBasePowerDescriptor.constant 2*2^w+53*(P*2^w)+53*(P*2^w*G)+
        (2*(BinaryPackedRowCount.powerBits w).length+2*(BinaryPackedRowCount.productBits P w).length+12)+59) := by
  have ha := active_input caller focus hf hs ht hh
  have h := Placement.hoare_at (BinaryPackedRowCount.constructs hs P w G hG hP hGv hw cP cG cw)
    (placement focus hf) (input caller) ha
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [native_output,← ha,PlacedDescriptorConstruction.replace_setTape,placement_active]
  simp only [slot,Fin.addCases]
  rfl

def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (rowSlot (t := t))

/-- Physically erase the retained count and restore the entire blank private
bank while preserving every original caller tape and head. -/
theorem cleans (caller : Tapes t a) (P w G : ℕ) :
    HoareTime cleanup (fun z => z=output caller P w G) (fun z => z=input caller)
      (2*(BinaryPackedRowCount.rowBits P w G).length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare rowSlot (output caller P w G)
    (BinaryPackedRowCount.rowBits P w G)
    (by simp only [output,setTape,Function.update_self,BinaryDescriptorStackRoundtrip.descriptor_encoded])
    (by simp only [output,setTape,Function.update_self])
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro z rfl
  rw [output,SharedPlacementAlphabet.setTape_setTape]
  have ht : (input caller).tape rowSlot=fun _ => blank := by
    simp [input,rowSlot,Tapes.append,FixedHeaderBankCopy.empty]
  have hh : (input caller).head rowSlot=0 := by
    simp [input,rowSlot,Tapes.append,FixedHeaderBankCopy.empty]
  rw [← ht,← hh,SharedPlacementAlphabet.setTape_self]

end
end IntegerMultBounds.Machine.BinaryPackedRowCountPlaced
