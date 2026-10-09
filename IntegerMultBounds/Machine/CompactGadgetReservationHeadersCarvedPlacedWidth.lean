import IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlaced

/-! Paid multiplication of two original physical descriptors, in the same
forty-tape private bank used by carved-header synthesis. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedWidth
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a : ℕ}

def ports : Fin 3 → Fin 40 := ![3,5,1]
theorem ports_injective : Function.Injective ports := by decide

def native (ws ns : List Bool) : Tapes 40 a :=
  (DimensionProductDescriptor.input ws ns).append (SharedBank.empty 34 a)
def program (focus : Fin 3 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (extend (DimensionProductDescriptor.program (q := a)) 34)
    (CleanSubbank.placement ports focus hf)

theorem constructs (caller : Tapes t a) (focus : Fin 3 → Fin t) (hf : Function.Injective focus)
    (ws ns : List Bool) (N W : ℕ) (hW : 0 < W)
    (hw : Counter.value ws = W) (hn : Counter.value ns = N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns)
    (h0 : caller.tape (focus 0) = RadixZeroFill.encodedBinary ws) (p0 : caller.head (focus 0) = 1)
    (h1 : caller.tape (focus 1) = RadixZeroFill.encodedBinary ns) (p1 : caller.head (focus 1) = 1)
    (h2 : caller.tape (focus 2) = fun _ => blank) (p2 : caller.head (focus 2) = 0) :
    HoareTime (program (a := a) focus hf)
      (fun v => v = CleanSubbank.bank (s := 40) caller)
      (fun v => v = CleanSubbank.bank (s := 40)
        (setTape caller (focus 2) (RadixZeroFill.encodedBinary (bits (N*W))) 1))
      (53*(N*W)+28) := by
  have h := hoare_extend_eq (DimensionProductDescriptor.construct_hoare ws ns N W hW hw hn cw cn)
    (SharedBank.empty 34 a)
  have he : DimensionProductDescriptor.output (q := a) ws ns N W =
      setTape (DimensionProductDescriptor.input ws ns) 1
        (RadixZeroFill.encodedBinary (bits (N*W))) 1 := by
    rw [← CompactGadgetReservationHeadersCore.canonical_bits (DimensionProductDescriptor.bits N W) (N*W)
      (DimensionProductDescriptor.bits_canonical N W) (DimensionProductDescriptor.bits_value N W)]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he,← SharedPlacementAlphabet.setTape_append_left] at h
  have hi : SharedBank.payload (native (a := a) ws ns) ports = SharedBank.payload caller focus := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [native,ports,DimensionProductDescriptor.input,
      Tapes.append,Fin.addCases,h0,h1,h2,p0,p1,p2]
  have hc : SharedBank.strip (native (a := a) ws ns) ports = SharedBank.empty 40 a := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [native,ports,DimensionProductDescriptor.input,
      Tapes.append,Fin.addCases,Fin.exists_fin_succ,SharedBank.empty]
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller
    (setTape caller (focus 2) (RadixZeroFill.encodedBinary (bits (N*W))) 1)
    (native ws ns) (setTape (native ws ns) (ports 2) (RadixZeroFill.encodedBinary (bits (N*W))) 1)
    _ hi ?_ hc ?_ ?_ h
  · simp only [CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,hi]
  · simpa only [CompactGadgetReservationPlacement.strip_set] using hc
  · simp only [CompactGadgetReservationPlacement.strip_set]

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCarvedPlacedWidth
