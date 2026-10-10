import IntegerMultBounds.Machine.FixedBasePowerDescriptor

/-! Construct the Q=2^w header used by packed-offset rotations from the sole
original width header. The fixed native power machine uses seven initially
blank slots, returns six clean, and retains only the generated Q header. -/
namespace IntegerMultBounds.Machine.PackedOffsetPowerHeader
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet

/-- Native output5 is caller Q7; native original exponent7 is caller width15. -/
def focus : Fin 8 → Fin 17 := ![0,1,2,3,4,7,9,15]

def placement : Fin (8+9) ≃ Fin 17 where
  toFun := ![0,1,2,3,4,7,9,15,5,6,8,10,11,12,13,14,16]
  invFun := ![0,1,2,3,4,8,9,5,10,6,11,12,13,14,15,7,16]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def program := Placement.placed (FixedBasePowerDescriptor.program (q := a) 2) placement

def output (caller : Tapes 17 a) (w : ℕ) :=
  setTape caller 7 (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (2^w))) 1

/-- Literal output word equality, including width zero. -/
theorem power_bits (w : ℕ) :
    FixedBasePowerStep.bits 2 w = RecursiveChildQuotientsConstant.bits (2^w) := by
  rw [RecursiveChildQuotientsConstant.bits_eq_advance]
  cases w with
  | zero => rfl
  | succ w => simp only [FixedBasePowerStep.bits,DimensionProductDescriptor.bits,
      pow_succ]

private theorem binary_eq (ws : List Bool) :
    CountedLoopReuseAlphabet.binary (a := a) ws=RadixZeroFill.encodedBinary ws := by
  exact (CountedLoopReuseAlphabet.encoding_binary ws).symm

def ScratchBlank (caller : Tapes 17 a) : Prop :=
  ∀ i : Fin 7, caller.head (focus (Fin.castAdd 1 i))=0 ∧
    caller.tape (focus (Fin.castAdd 1 i))=fun _ => blank

private theorem active_input (caller : Tapes 17 a) (ws : List Bool)
    (hs : ScratchBlank caller)
    (ht : caller.tape 15=RadixZeroFill.encodedBinary ws) (hh : caller.head 15=1) :
    Placement.active placement caller=FixedBasePowerDescriptor.input ws := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i
    · exact (hs 0).1
    · exact (hs 1).1
    · exact (hs 2).1
    · exact (hs 3).1
    · exact (hs 4).1
    · exact (hs 5).1
    · exact (hs 6).1
    · exact hh
  · funext i; fin_cases i
    · exact (hs 0).2
    · exact (hs 1).2
    · exact (hs 2).2
    · exact (hs 3).2
    · exact (hs 4).2
    · exact (hs 5).2
    · exact (hs 6).2
    · exact ht.trans (binary_eq ws).symm

private theorem replaced_output (caller : Tapes 17 a) (w : ℕ) (ws : List Bool)
    (hs : ScratchBlank caller)
    (ht : caller.tape 15=RadixZeroFill.encodedBinary ws) (hh : caller.head 15=1) :
    Placement.replace placement caller (FixedBasePowerDescriptor.output 2 w ws)=output caller w := by
  apply congrArg₂ Tapes.mk
  · funext i
    fin_cases i <;> first | rfl | exact (hs 0).1.symm | exact (hs 1).1.symm | exact (hs 2).1.symm | exact (hs 3).1.symm | exact (hs 4).1.symm | exact (hs 6).1.symm | exact hh.symm
  · funext i
    fin_cases i <;> first | rfl | exact (hs 0).2.symm | exact (hs 1).2.symm | exact (hs 2).2.symm | exact (hs 3).2.symm | exact (hs 4).2.symm | exact (hs 6).2.symm | exact (binary_eq ws).trans ht.symm | exact congrArg (RadixZeroFill.encodedBinary (q := a)) (power_bits w)

/-- The original runtime exponent is retained and all native scratch is clean.
No supplied Q descriptor or preinitialized numeric workspace is needed. -/
theorem constructs (caller : Tapes 17 a) (w : ℕ) (ws : List Bool)
    (hw : Counter.value ws=w) (hs : ScratchBlank caller)
    (ht : caller.tape 15=RadixZeroFill.encodedBinary ws) (hh : caller.head 15=1) :
    HoareTime program (fun v => v=caller) (fun v => v=output caller w)
      (FixedBasePowerDescriptor.exactCost 2 w ws) := by
  have h := Placement.hoare_at (FixedBasePowerDescriptor.constructs (q := a) 2 w (by decide) ws hw)
    placement caller (active_input caller ws hs ht hh)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  exact replaced_output caller w ws hs ht hh

/-- A bound in the generated power, with no assumption that a payload exists. -/
theorem constructs_linear (caller : Tapes 17 a) (w : ℕ) (ws : List Bool)
    (hw : Counter.value ws=w) (cw : GrowingCounterData.Canonical ws) (hs : ScratchBlank caller)
    (ht : caller.tape 15=RadixZeroFill.encodedBinary ws) (hh : caller.head 15=1) :
    HoareTime program (fun v => v=caller) (fun v => v=output caller w)
      (FixedBasePowerDescriptor.constant 2*2^w) :=
  (constructs caller w ws hw hs ht hh).consequence (fun _ h => h) (fun _ h => h)
    (FixedBasePowerDescriptor.cost_linear 2 w (by decide) ws hw cw)

def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (7 : Fin 17)

/-- Actual erasure of the generated Q header and return of its head to zero. -/
theorem cleans (caller : Tapes 17 a) (w : ℕ)
    (ht : caller.tape 7=fun _ => blank) (hh : caller.head 7=0) :
    HoareTime cleanup (fun v => v=output caller w) (fun v => v=caller)
      (2*(RecursiveChildQuotientsConstant.bits (2^w)).length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (7 : Fin 17) (output caller w)
    (RecursiveChildQuotientsConstant.bits (2^w))
    (by simp only [output,setTape,Function.update_self,BinaryDescriptorStackRoundtrip.descriptor_encoded])
    (by simp only [output,setTape,Function.update_self])
  simpa only [cleanup,output,setTape_setTape,← ht,← hh,setTape_self] using h

/-- Every original input and native scratch slot except Q is literally framed. -/
theorem output_frame (caller : Tapes 17 a) (w : ℕ) (i : Fin 17) (hi : i≠7) :
    (output caller w).head i=caller.head i ∧ (output caller w).tape i=caller.tape i := by
  simp [output,setTape,hi]

theorem output_header (caller : Tapes 17 a) (w : ℕ) :
    (output caller w).head 7=1 ∧ (output caller w).tape 7=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (2^w)) := by
  exact ⟨rfl,rfl⟩

/-- Cleanup cost is charged to the actual generated power, independently of n. -/
theorem cleanup_bound (w : ℕ) :
    2*(RecursiveChildQuotientsConstant.bits (2^w)).length+4 ≤ 8*2^w := by
  have hl := GrowingCounterData.canonical_width (RecursiveChildQuotientsConstant.bits (2^w))
    (RecursiveChildQuotientsConstant.bits_canonical (2^w))
  rw [RecursiveChildQuotientsConstant.bits_value] at hl
  have hn := Nat.log2_le_self (2^w)
  have hp : 1 ≤ 2^w := Nat.one_le_pow _ _ (by decide)
  omega

theorem cleans_linear (caller : Tapes 17 a) (w : ℕ)
    (ht : caller.tape 7=fun _ => blank) (hh : caller.head 7=0) :
    HoareTime cleanup (fun v => v=output caller w) (fun v => v=caller) (8*2^w) :=
  (cleans caller w ht hh).consequence (fun _ h => h) (fun _ h => h) (cleanup_bound w)

end
end IntegerMultBounds.Machine.PackedOffsetPowerHeader
