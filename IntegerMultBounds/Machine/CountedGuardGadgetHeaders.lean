import IntegerMultBounds.Machine.BinaryDescriptorDifference

/-! Original-width preparation for the fixed runtime guard gadget. The original
q header is retained; one is physically written on blank private storage,
canonical q−1 is computed, and the temporary one is physically erased. -/
namespace IntegerMultBounds.Machine.CountedGuardGadgetHeaders
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet

theorem binary_eq (ws : List Bool) :
    CountedLoopReuseAlphabet.binary (a := a) ws = RadixZeroFill.encodedBinary ws :=
  (CountedLoopReuseAlphabet.encoding_binary ws).symm

def input (qs : List Bool) : Tapes 3 a :=
  ⟨![1,0,0],![CountedLoopReuseAlphabet.binary qs,fun _ => blank,fun _ => blank]⟩

def prepared (qs : List Bool) : Tapes 3 a := BinaryDescriptorDifference.input qs (RecursiveChildQuotientsConstant.bits 1)
def output (qs : List Bool) (q : ℕ) :=
  setTape (input (a := a) qs) 2 (BinaryDescriptorStack.descriptor (RecursiveChildQuotientsConstant.bits (q-1))) 1

def oneProgram := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement (1 : Fin 3))
def cleanupOne := BinaryDescriptorCleanupList.oneProgram (a := a) (1 : Fin 3)
def cleanup := BinaryDescriptorCleanupList.oneProgram (a := a) (2 : Fin 3)
def program := seq (seq (oneProgram (a := a)) BinaryDescriptorDifference.program) cleanupOne

private theorem one_hoare (qs : List Bool) :
    HoareTime (oneProgram (a := a)) (fun v => v=input qs) (fun v => v=prepared qs)
      (RecursiveChildQuotientsConstant.cost 1) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement (1 : Fin 3)) (input (a := a) qs)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  refine h.consequence (fun _ h => h) ?_ le_rfl
  rintro v ⟨z,rfl,rfl⟩
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem constructs (qs : List Bool) (q : ℕ) (hq : Counter.value qs=q)
    (cq : GrowingCounterData.Canonical qs) (hp : 1 ≤ q) :
    HoareTime (program (a := a)) (fun v => v=input qs) (fun v => v=output qs q) (6*q+44) := by
  have h1 := one_hoare (a := a) qs
  have h2 := BinaryDescriptorDifference.difference_linear (a := a) qs (RecursiveChildQuotientsConstant.bits 1)
    (by rw [RecursiveChildQuotientsConstant.bits_value,hq]; exact hp)
    cq (RecursiveChildQuotientsConstant.bits_canonical 1)
  rw [RecursiveChildQuotientsConstant.bits_value,hq] at h2
  have h3 := BinaryDescriptorCleanupList.one_hoare (1 : Fin 3)
    (BinaryDescriptorDifference.output (a := a) qs (RecursiveChildQuotientsConstant.bits 1)
      (RecursiveChildQuotientsConstant.bits (q-1))) (RecursiveChildQuotientsConstant.bits 1)
    (by change CountedLoopReuseAlphabet.binary _ = BinaryDescriptorStack.descriptor _
        rw [BinaryDescriptorStackRoundtrip.descriptor_encoded,binary_eq]) rfl
  have he : setTape (BinaryDescriptorDifference.output (a := a) qs (RecursiveChildQuotientsConstant.bits 1)
      (RecursiveChildQuotientsConstant.bits (q-1))) 1 (fun _ => blank) 0 = output qs q := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h3
  exact ((h1.seq h2).seq h3).consequence (fun _ h => h) (fun _ h => h) (by
    norm_num [RecursiveChildQuotientsConstant.cost,RecursiveChildQuotientsConstant.bits,
      GrowingCounterData.advance,GrowingCounterData.increment]
    omega)

theorem cleans (qs : List Bool) (q : ℕ) :
    HoareTime (cleanup (a := a)) (fun v => v=output qs q) (fun v => v=input qs)
      (2*(RecursiveChildQuotientsConstant.bits (q-1)).length+4) := by
  have h := BinaryDescriptorCleanupList.one_hoare (2 : Fin 3) (output (a := a) qs q)
    (RecursiveChildQuotientsConstant.bits (q-1)) rfl rfl
  simpa only [cleanup,output,setTape_setTape,← show (input (a := a) qs).tape 2=(fun _ => blank) from rfl,
    ← show (input (a := a) qs).head 2=0 from rfl,setTape_self] using h

end
end IntegerMultBounds.Machine.CountedGuardGadgetHeaders
