import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCore
import IntegerMultBounds.Machine.BinaryDescriptorCopyPlaced
import IntegerMultBounds.Machine.ActiveRepairRankHeadersCommands
import IntegerMultBounds.Machine.BinaryDescriptorIncrement

/-! Runtime descent decrements the retained canonical exponent word. A fixed
three-tape machine writes its own one, subtracts, replaces the exponent, and
physically clears both work tapes; no child exponent word is supplied. -/
namespace IntegerMultBounds.Machine.CompactComplexExponentStep
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def bank (e : ℕ) : Tapes 3 a :=
  ⟨![1,0,0],![BinaryDescriptorStack.descriptor (bits e),fun _ => blank,fun _ => blank]⟩
def oneProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement (1 : Fin 3))
def copyFocus : Fin 2 → Fin 3 := ![2,0]
theorem copy_injective : Function.Injective copyFocus := by decide

def program := seq (oneProgram (a := a))
  (seq (BinaryDescriptorDifference.program (a := a))
    (seq (BinaryDescriptorCleanupList.oneProgram (a := a) (0 : Fin 3))
      (seq (BinaryDescriptorCopyPlaced.program (a := a) copyFocus copy_injective)
        (seq (BinaryDescriptorCleanupList.oneProgram (a := a) (1 : Fin 3))
          (BinaryDescriptorCleanupList.oneProgram (a := a) (2 : Fin 3))))))

private theorem descriptor_counted (xs : List Bool) :
    BinaryDescriptorStack.descriptor (a := a) xs = CountedLoopReuseAlphabet.binary xs := by
  rw [BinaryDescriptorStackRoundtrip.descriptor_encoded,CompactGadgetReservationHeadersCore.encoded_binary]

private theorem oneProgram_runs (e : ℕ) : HoareTime (oneProgram (a := a))
    (fun v => v=bank e) (fun v => v=BinaryDescriptorDifference.input (bits e) (bits 1))
    (RecursiveChildQuotientsConstant.cost 1) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement (1 : Fin 3)) (bank (a := a) e)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals simp [bank,descriptor_counted]

/-- Every transition including replacement and cleanup is paid. Exponent zero
is deliberately excluded: scalar leaves take their separate terminal branch. -/
theorem runs (e : ℕ) (he : 0 < e) : HoareTime (program (a := a))
    (fun v => v=bank e) (fun v => v=bank (e-1)) (20*(e+1)+100) := by
  let diff := BinaryDescriptorDifference.output (a := a) (bits e) (bits 1) (bits (e-1))
  let erased := setTape diff 0 (fun _ => blank) 0
  let moved := setTape erased 0 (RadixZeroFill.encodedBinary (bits (e-1))) 1
  let cleanOne := setTape moved 1 (fun _ => blank) 0
  have hd := BinaryDescriptorDifference.difference_linear (a := a) (bits e) (bits 1)
    (by simp only [RecursiveChildQuotientsConstant.bits_value]; omega)
    (RecursiveChildQuotientsConstant.bits_canonical e) (RecursiveChildQuotientsConstant.bits_canonical 1)
  simp only [RecursiveChildQuotientsConstant.bits_value] at hd
  have h0 := BinaryDescriptorCleanupList.one_hoare (0 : Fin 3) diff (bits e)
    (by simp [diff,BinaryDescriptorDifference.output,BinaryDescriptorDifference.bank,descriptor_counted]) (by rfl)
  have hc := BinaryDescriptorCopyPlaced.copies erased copyFocus copy_injective (bits (e-1)) (by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [copyFocus,erased,diff,BinaryDescriptorDifference.output,
        BinaryDescriptorDifference.bank,Copy.cfg,
        setTape,BinaryDescriptorStackRoundtrip.descriptor_encoded])
  have h1 := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3) moved (bits 1)
    (by simp [moved,erased,diff,BinaryDescriptorDifference.output,BinaryDescriptorDifference.bank,
      setTape,descriptor_counted]) (by rfl)
  have h2 := BinaryDescriptorCleanupList.one_hoare (2 : Fin 3) cleanOne (bits (e-1))
    (by simp [cleanOne,moved,erased,diff,BinaryDescriptorDifference.output,BinaryDescriptorDifference.bank,
      setTape]) (by rfl)
  have h := (oneProgram_runs (a := a) e).seq (hd.seq (h0.seq (hc.seq (h1.seq h2))))
  have hle := ActiveRepairRankHeadersCommands.bits_length e
  have hpred := ActiveRepairRankHeadersCommands.bits_length (e-1)
  have hone := ActiveRepairRankHeadersCommands.bits_length 1
  apply h.consequence (fun _ h => h) _ (by simp [RecursiveChildQuotientsConstant.cost]; omega)
  intro v hv
  rw [hv]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [cleanOne,moved,erased,diff,BinaryDescriptorDifference.output,
      BinaryDescriptorDifference.bank,setTape,BinaryDescriptorStackRoundtrip.descriptor_encoded]


private theorem output_eq (e : ℕ) : bank (a := a) (e-1) =
    setTape (bank e) 0 (BinaryDescriptorStack.descriptor (bits (e-1))) 1 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

/-- Place the exponent plus two clean work tapes outside a native bank.
All complementary tapes and heads are retained by the actual execution. -/
theorem runs_at {u t : ℕ} (placement : Fin (3+u) ≃ Fin t) (v : Tapes t a) (e : ℕ)
    (he : 0 < e) (hi : Placement.active placement v = bank e) :
    HoareTime (Placement.placed (program (a := a)) placement) (fun w => w=v)
      (fun w => w=setTape v (placement (Fin.castAdd u (0 : Fin 3)))
        (BinaryDescriptorStack.descriptor (bits (e-1))) 1) (20*(e+1)+100) := by
  have h := Placement.hoare_at (runs (a := a) e he) placement v hi
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  rw [output_eq,← hi,PlacedDescriptorConstruction.replace_setTape]


def ascendProgram {t : ℕ} (slot : Fin t) :=
  Placement.placed (BinaryDescriptorIncrement.program (q := a)) (FiniteReturnStackAt.placement slot)

/-- Returning from one child increments its retained exponent in place, so
an extra exponent-stack copy is unnecessary. -/
theorem ascend {t : ℕ} (slot : Fin t) (v : Tapes t a) (e : ℕ)
    (ht : v.tape slot = BinaryDescriptorStack.descriptor (bits e)) (hh : v.head slot = 1) :
    HoareTime (ascendProgram (a := a) slot) (fun w => w=v)
      (fun w => w=setTape v slot (BinaryDescriptorStack.descriptor (bits (e+1))) 1) (2*(e+2)) := by
  have heq : GrowingCounterData.increment (bits e) = bits (e+1) :=
    BinaryCanonicalData.value_injective _ _
      (BinaryDescriptorIncrement.canonical _ (RecursiveChildQuotientsConstant.bits_canonical e))
      (RecursiveChildQuotientsConstant.bits_canonical (e+1)) (by
        rw [BinaryDescriptorIncrement.value,RecursiveChildQuotientsConstant.bits_value,
          RecursiveChildQuotientsConstant.bits_value])
  have h := Placement.hoare_at (BinaryDescriptorIncrement.increment_linear (q := a) (bits e))
    (FiniteReturnStackAt.placement slot) v
    (by rw [FiniteReturnStackAt.active_bank,ht,hh]; rfl)
  have hl := ActiveRepairRankHeadersCommands.bits_length e
  apply h.consequence (fun _ h => h) _ (by omega)
  rintro w ⟨z,rfl,rfl⟩
  rw [heq]
  change Placement.replace (FiniteReturnStackAt.placement slot) v
    (FiniteReturnStack.bank (BinaryDescriptorStack.descriptor (bits (e+1))) 1) = _
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem ascend_parent {t : ℕ} (slot : Fin t) (v : Tapes t a) (e : ℕ) (he : 0 < e)
    (ht : v.tape slot = BinaryDescriptorStack.descriptor (bits (e-1))) (hh : v.head slot = 1) :
    HoareTime (ascendProgram (a := a) slot) (fun w => w=v)
      (fun w => w=setTape v slot (BinaryDescriptorStack.descriptor (bits e)) 1) (2*(e+1)) := by
  have h := ascend slot v (e-1) ht hh
  have hpred : e-1+1 = e := by omega
  rw [hpred] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CompactComplexExponentStep
