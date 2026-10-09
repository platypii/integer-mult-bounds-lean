import IntegerMultBounds.Machine.CompactGadgetReservationPlacement
import IntegerMultBounds.Machine.PlacedDescriptorConstruction
import IntegerMultBounds.Machine.BinaryDescriptorDifference
import IntegerMultBounds.Machine.RoundedRowDescriptor

/-! Fixed clean descriptor primitives share one fifteen-tape private bank.
Every operand is a physical marked word; every output begins blank. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationHeadersCore
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {t a k q : ℕ}

theorem encoded_binary (xs : List Bool) :
    RadixZeroFill.encodedBinary (q := a) xs = CountedLoopReuseAlphabet.binary xs :=
  CountedLoopReuseAlphabet.encoding_binary xs

def bank (v : Tapes t a) := CleanSubbank.bank (s := 15) v

def placed (M : Program 15 q a) (ports : Fin k → Fin 15)
    (focus : Fin k → Fin t) (hf : Function.Injective focus) :=
  Placement.placed M (CleanSubbank.placement ports focus hf)

/-- One output is physically synthesized; all other permanent tapes and the
shared private bank are retained. This lift introduces no copies or moves. -/
theorem single (M : Program 15 q a) (ports : Fin k → Fin 15)
    (hp : Function.Injective ports) (focus : Fin k → Fin t) (hf : Function.Injective focus)
    (v : Tapes t a) (X : Tapes 15 a) (i : Fin k) (zs : List Bool) (C : ℕ)
    (hsel : SharedBank.payload X ports = SharedBank.payload v focus)
    (hclean : SharedBank.strip X ports = SharedBank.empty 15 a)
    (hr : HoareTime M (fun u => u = X)
      (fun u => u = setTape X (ports i) (RadixZeroFill.encodedBinary zs) 1) C) :
    HoareTime (placed M ports focus hf) (fun u => u = bank v)
      (fun u => u = bank (setTape v (focus i) (RadixZeroFill.encodedBinary zs) 1)) C := by
  let e := CleanSubbank.placement ports focus hf
  have ha := CleanSubbank.active_bank ports focus hp hf v X hsel hclean
  have h := Placement.hoare_at hr e (bank v) ha
  refine h.consequence (fun _ h => h) ?_ (le_refl _)
  rintro u ⟨small,rfl,rfl⟩
  rw [← ha]
  change Placement.replace e (bank v) (setTape (Placement.active e (bank v))
    (ports i) (RadixZeroFill.encodedBinary zs) 1) = _
  rw [PlacedDescriptorConstruction.replace_setTape]
  dsimp only [e]
  rw [CleanSubbank.placement_active,CleanSubbank.slot_selected ports focus hp]
  exact SharedPlacementAlphabet.setTape_append_left _ _ _ _ _

theorem canonical_bits (xs : List Bool) (N : ℕ)
    (hx : GrowingCounterData.Canonical xs) (hv : Counter.value xs = N) : xs = bits N :=
  BinaryCanonicalData.value_injective xs (bits N) hx
    (RecursiveChildQuotientsConstant.bits_canonical N)
    (hv.trans (RecursiveChildQuotientsConstant.bits_value N).symm)

def productPorts : Fin 3 → Fin 15 := fun i => Fin.castAdd 9 (![3,5,1] i : Fin 6)
theorem product_injective : Function.Injective productPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [productPorts]
def productCore := extend (DimensionProductDescriptor.program (q := a)) 9
def productProgram (focus : Fin 3 → Fin t) (hf : Function.Injective focus) :=
  placed (productCore (a := a)) productPorts focus hf

theorem product (v : Tapes t a) (focus : Fin 3 → Fin t) (hf : Function.Injective focus)
    (ws ns : List Bool) (N W : ℕ) (hW : 0 < W)
    (hw : Counter.value ws = W) (hn : Counter.value ns = N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical ns)
    (h0 : v.tape (focus 0) = RadixZeroFill.encodedBinary ws) (p0 : v.head (focus 0) = 1)
    (h1 : v.tape (focus 1) = RadixZeroFill.encodedBinary ns) (p1 : v.head (focus 1) = 1)
    (h2 : v.tape (focus 2) = fun _ => blank) (p2 : v.head (focus 2) = 0) :
    HoareTime (productProgram (a := a) focus hf) (fun u => u = bank v)
      (fun u => u = bank (setTape v (focus 2) (RadixZeroFill.encodedBinary (bits (N*W))) 1))
      (53*(N*W)+28) := by
  let X := (DimensionProductDescriptor.input (q := a) ws ns).append (SharedBank.empty 9 a)
  have hr := hoare_extend_eq (DimensionProductDescriptor.construct_hoare ws ns N W hW hw hn cw cn)
    (SharedBank.empty 9 a)
  have he : DimensionProductDescriptor.output (q := a) ws ns N W =
      setTape (DimensionProductDescriptor.input ws ns) 1
        (RadixZeroFill.encodedBinary (bits (N*W))) 1 := by
    rw [← canonical_bits (DimensionProductDescriptor.bits N W) (N*W)
      (DimensionProductDescriptor.bits_canonical N W) (DimensionProductDescriptor.bits_value N W)]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at hr
  rw [← SharedPlacementAlphabet.setTape_append_left] at hr
  apply single (productCore (a := a)) productPorts product_injective focus hf v X 2 _ _ ?_ ?_ hr
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,productPorts,DimensionProductDescriptor.input,Tapes.append,Fin.addCases,h0,h1,h2,p0,p1,p2]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,productPorts,DimensionProductDescriptor.input,Tapes.append,Fin.addCases,Fin.exists_fin_succ,SharedBank.empty]

def differencePorts : Fin 3 → Fin 15 := Fin.castAdd 12
theorem difference_injective : Function.Injective differencePorts := by
  intro i j h
  exact Fin.castAdd_injective _ _ h
def differenceCore := extend (BinaryDescriptorDifference.program (a := a)) 12
def differenceProgram (focus : Fin 3 → Fin t) (hf : Function.Injective focus) :=
  placed (differenceCore (a := a)) differencePorts focus hf

theorem difference (v : Tapes t a) (focus : Fin 3 → Fin t) (hf : Function.Injective focus)
    (xs ys : List Bool) (hle : Counter.value ys ≤ Counter.value xs)
    (cx : GrowingCounterData.Canonical xs) (cy : GrowingCounterData.Canonical ys)
    (h0 : v.tape (focus 0) = RadixZeroFill.encodedBinary xs) (p0 : v.head (focus 0) = 1)
    (h1 : v.tape (focus 1) = RadixZeroFill.encodedBinary ys) (p1 : v.head (focus 1) = 1)
    (h2 : v.tape (focus 2) = fun _ => blank) (p2 : v.head (focus 2) = 0) :
    HoareTime (differenceProgram (a := a) focus hf) (fun u => u = bank v)
      (fun u => u = bank (setTape v (focus 2)
        (RadixZeroFill.encodedBinary (bits (Counter.value xs-Counter.value ys))) 1))
      (6*Counter.value xs+27) := by
  let X := (BinaryDescriptorDifference.input (a := a) xs ys).append (SharedBank.empty 12 a)
  have hr := hoare_extend_eq (BinaryDescriptorDifference.difference_linear (a := a) xs ys hle cx cy)
    (SharedBank.empty 12 a)
  have he : BinaryDescriptorDifference.output (a := a) xs ys
      (bits (Counter.value xs-Counter.value ys)) =
      setTape (BinaryDescriptorDifference.input xs ys) 2
        (RadixZeroFill.encodedBinary (bits (Counter.value xs-Counter.value ys))) 1 := by
    rw [BinaryDescriptorDifference.output,BinaryDescriptorStackRoundtrip.descriptor_encoded]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he,← SharedPlacementAlphabet.setTape_append_left] at hr
  apply single (differenceCore (a := a)) differencePorts difference_injective focus hf v X 2 _ _ ?_ ?_ hr
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,differencePorts,BinaryDescriptorDifference.input,
      BinaryDescriptorDifference.bank,Tapes.append,Fin.addCases,h0,h1,h2,p0,p1,p2,encoded_binary]
  · apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals simp [X,differencePorts,BinaryDescriptorDifference.input,
      BinaryDescriptorDifference.bank,Tapes.append,Fin.addCases,Fin.exists_fin_succ,SharedBank.empty]

end
end IntegerMultBounds.Machine.CompactGadgetReservationHeadersCore
