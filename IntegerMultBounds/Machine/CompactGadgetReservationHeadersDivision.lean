import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCore
import IntegerMultBounds.Machine.BinaryDescriptorDivision

/-! Physical quotient synthesis in the same clean fifteen-tape workspace. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersDivision
noncomputable section
open CompactGadgetReservationHeadersCore
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def ports : Fin 3 → Fin 15 := fun i => Fin.castAdd 3 (![0,1,5] i : Fin 12)
theorem ports_injective : Function.Injective ports := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [ports]
def core := extend (BinaryDescriptorDivision.program a) 3
def program (focus : Fin 3 → Fin t) (hf : Function.Injective focus) :=
  placed (core (a := a)) ports focus hf

theorem divides (v : Tapes t a) (focus : Fin 3 → Fin t) (hf : Function.Injective focus)
    (rs ds : List Bool) (hd : 0 < Counter.value ds)
    (h0 : v.tape (focus 0) = RadixZeroFill.encodedBinary rs) (p0 : v.head (focus 0) = 1)
    (h1 : v.tape (focus 1) = RadixZeroFill.encodedBinary ds) (p1 : v.head (focus 1) = 1)
    (h2 : v.tape (focus 2) = fun _ => blank) (p2 : v.head (focus 2) = 0) :
    HoareTime (program (a := a) focus hf) (fun u => u = bank v)
      (fun u => u = bank (setTape v (focus 2)
        (RadixZeroFill.encodedBinary (bits (Counter.value rs / Counter.value ds))) 1))
      (BinaryDescriptorDivision.cost rs ds) := by
  obtain ⟨zs,hc,hv,_,hr0⟩ := BinaryDescriptorDivision.divide_hoare (a := a) rs ds hd
  have hz : zs = bits (Counter.value rs / Counter.value ds) := canonical_bits _ _ hc hv
  subst zs
  let X := (BinaryDescriptorDivision.input (a := a) rs ds).append (SharedBank.empty 3 a)
  have hout : BinaryDescriptorDivision.output (a := a) rs ds (bits (Counter.value rs / Counter.value ds)) =
      setTape (BinaryDescriptorDivision.input rs ds) 5
        (RadixZeroFill.encodedBinary (bits (Counter.value rs / Counter.value ds))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [BinaryDescriptorDivision.retained,
      BinaryDescriptorDivision.input,BinaryDescriptorDivisionBoundary.input,
      BinaryDescriptorDivisionRaw.bank,Tapes.append,Fin.addCases,
      BinaryDescriptorStackRoundtrip.descriptor_encoded]
  rw [hout] at hr0
  have hr := hoare_extend_eq hr0 (SharedBank.empty 3 a)
  rw [← SharedPlacementAlphabet.setTape_append_left] at hr
  apply single (core (a := a)) ports ports_injective focus hf v X 2 _ _ ?_ ?_ hr
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,ports,BinaryDescriptorDivision.input,
      BinaryDescriptorDivisionBoundary.input,BinaryDescriptorDivisionRaw.bank,
      Tapes.append,Fin.addCases,h0,h1,h2,p0,p1,p2,
      BinaryDescriptorStackRoundtrip.descriptor_encoded]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,ports,BinaryDescriptorDivision.input,
      BinaryDescriptorDivisionBoundary.input,BinaryDescriptorDivisionRaw.bank,
      Tapes.append,Fin.addCases,Fin.exists_fin_succ,SharedBank.empty]

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersDivision
