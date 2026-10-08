import IntegerMultBounds.Machine.RecursiveShiftInitialize
import IntegerMultBounds.Machine.RecursiveInterchangeShift

/-! A complete initialized and normalized seven-factor H-controlled D shift.
Only six canonical layout headers and one array are supplied. All products,
control digits, markers, copies, joins, and payload head restoration are real
machine operations. Generated metadata remains explicit at the output. -/
namespace IntegerMultBounds.Machine.RecursiveInterchangeShiftConstruct
open RecursiveInterchangeLayout (Descriptor volume)
open Networks
open Shared50ModularControl (prime)
noncomputable section
local instance : Fact prime.Prime := ⟨Shared50ModularControl.prime_prime⟩

def source {v : Descriptor} (a : Fin (volume prime v) → Fin 4) := putWord (fun _ => blank) 0 (List.ofFn a)
def dims (v : Descriptor) (hs : Fin 6 → List Bool) := RecursiveShiftInitialize.dimensions (q := prime) v hs

def input {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :=
  RecursiveShiftInitialize.input (q := prime) hs (source a)

def dimensionBank (v : Descriptor) (hs : Fin 6 → List Bool) :=
  RecursiveDimensionBank.bank (q := prime) hs (RecursiveDimensionBank.ds4 (Fact.out : prime.Prime).two_le v)

def output {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :=
  (dimensionBank v hs).append ((RecursiveInterchangeShift.output r a (dims v hs 0) (dims v hs 1)
    (dims v hs 2) (dims v hs 3)).append (RepeatedControlBootstrap.widthTape (dims v hs 4)))

def program (r : ℚ) := seq (RecursiveShiftInitialize.program (q := prime))
  (Placement.placed (extend (RecursiveInterchangeShift.program r) 1) finAddFlip)

private theorem left_frame {n s q a k : ℕ} {M : Program n s a} {x y : Tapes n a}
    (h : HoareTime M (fun v => v = x) (fun v => v = y) k) (v : Tapes q a) :
    HoareTime (Placement.placed M (finAddFlip : Fin (n+q) ≃ Fin (q+n)))
      (fun w => w = v.append x) (fun w => w = v.append y) k := by
  have he (z : Tapes n a) : Placement.combine finAddFlip z v = v.append z := by
    apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases <;>
      simp [Tapes.append,finAddFlip]
  have hh := Placement.hoare_at h finAddFlip (Placement.combine finAddFlip x v)
    (Placement.active_combine _ _ _)
  apply hh.consequence (fun w hw => hw.trans (he x).symm) _ le_rfl
  rintro w ⟨z,hz,rfl⟩
  subst z
  simpa only [Placement.replace,Placement.extra_combine] using he y

private theorem prepared_input {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) :
    RecursiveShiftInitialize.output v hs (source a) =
      (dimensionBank v hs).append ((RecursiveInterchangeShift.input r a (dims v hs 0) (dims v hs 1)
        (dims v hs 2) (dims v hs 3)).append (RepeatedControlBootstrap.widthTape (dims v hs 4))) := by
  unfold RecursiveShiftInitialize.output dimensionBank RepeatedControlBootstrap.output
    RecursiveInterchangeShift.input FlatRepeatedControlShift.state RepeatedControlTranslationStream.state
  simp only [Nat.zero_mul,Nat.cast_zero,add_zero,FlatRepeatedControlShift.source_eq,
    RepeatedControlTranslationStream.outputPrefix,List.range_zero,List.map_nil,List.flatten_nil,
    RecursiveInterchangeShift.view_word]
  rfl

theorem constructs_hoare {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program r) (fun w => w = input hs a) (fun w => w = output r hs a)
      (1288*volume prime v+186) := by
  have hi := RecursiveShiftInitialize.construct_hoare_linear (q := prime) v hs (source a) hv hvpos
  rw [prepared_input r] at hi
  have hd := RecursiveDimensionBank.dimensions (Fact.out : prime.Prime).two_le v
  have ht := RecursiveInterchangeShift.realizes_hoare r a hvpos (dims v hs 0) (dims v hs 1)
    (dims v hs 2) (dims v hs 3) (hv.1 5) hd.1 (hv.1 4) hd.2.1
    (hv.2 5) hd.2.2.1 (hv.2 4) hd.2.2.2
  have he := hoare_extend_eq ht (RepeatedControlBootstrap.widthTape (dims v hs 4))
  have hh := hi.seq (left_frame he (dimensionBank v hs))
  exact hh.consequence (fun _ h => h) (fun _ h => h) (by omega)

def sourceSlot : Fin 34 := Fin.natAdd 13 (Fin.castAdd 1 (10 : Fin 20))
def destSlot : Fin 34 := Fin.natAdd 13 (Fin.castAdd 1 (11 : Fin 20))

theorem input_payload {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :
    SharedPayload.payload (input hs a) sourceSlot destSlot = FlatRepeatedControlArray.pair a := by
  unfold input RecursiveShiftInitialize.input SharedPayload.payload sourceSlot destSlot
  simp only [Tapes.append,Fin.addCases_right,RecursiveShiftInstall.blankLocal]
  rfl

theorem output_payload {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4) :
    SharedPayload.payload (output r hs a) sourceSlot destSlot =
      FlatRepeatedControlArray.pair (RecursiveInterchangeShift.array r a) := by
  unfold output SharedPayload.payload sourceSlot destSlot
  simp only [Tapes.append,Fin.addCases_right,Fin.addCases_left]
  exact RecursiveInterchangeShift.output_payload r a _ _ _ _

/-- Every input tape outside the headers and sole source is genuinely blank. -/
theorem input_local_blank {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4)
    (i : Fin 21) (hi : i ≠ 10) :
    (input hs a).head (Fin.natAdd 13 i) = 0 ∧
    (input hs a).tape (Fin.natAdd 13 i) = (fun _ => blank) := by
  simp [input,RecursiveShiftInitialize.input,Tapes.append,RecursiveShiftInstall.blankLocal,hi]

/-- Only the six retained layout headers are nonblank in the input dimension bank. -/
theorem input_dimension_blank {v : Descriptor} (hs : Fin 6 → List Bool) (a : Fin (volume prime v) → Fin 4)
    (i : Fin 13) (hi : i.val < 3 ∨ 9 ≤ i.val) :
    (input hs a).head (Fin.castAdd 21 i) = 0 ∧
    (input hs a).tape (Fin.castAdd 21 i) = (fun _ => blank) := by
  unfold input RecursiveShiftInitialize.input
  simp only [Tapes.append,Fin.addCases_left]
  fin_cases i <;> norm_num at hi <;> exact ⟨rfl,rfl⟩

theorem headers_preserved {v : Descriptor} (r : ℚ) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (i : Fin 6) :
    (output r hs a).head (Fin.castAdd 21 (Fin.castAdd 4 (Fin.natAdd 3 i))) = 1 ∧
    (output r hs a).tape (Fin.castAdd 21 (Fin.castAdd 4 (Fin.natAdd 3 i))) = RadixZeroFill.encodedBinary (hs i) := by
  unfold output dimensionBank
  simp only [Tapes.append,Fin.addCases_left]
  exact RecursiveDimensionBank.headers_preserved hs _ i

/-- Full physical execution and literal H-controlled D semantics, from sole
canonical headers and payload rather than a generated metadata premise. -/
theorem constructs_array {v : Descriptor} (r : ℚ) (hden : r.den < prime) (hs : Fin 6 → List Bool)
    (a : Fin (volume prime v) → Fin 4) (hv : RecursiveDimensionBank.Headers v hs) (hvpos : v.Positive) :
    HoareTime (program r) (fun w => w = input hs a)
      (fun w => w = output r hs a ∧
        SharedPayload.payload w sourceSlot destSlot = FlatRepeatedControlArray.pair (RecursiveInterchangeShift.array r a) ∧
        ∀ x : RecursiveInterchangeScaling.Address v,
          RecursiveInterchangeShift.array r a (RecursiveInterchangeScaling.index (RecursiveInterchangeShift.shiftAddress r x)) =
            a (RecursiveInterchangeScaling.index x) ∧
          (RecursiveInterchangeShift.shiftAddress r x).d.val =
            (x.d.val+(Swap.Modular.ratMod (ActualAffineScaling.modulus v.width) r*
              (x.h.val : ZMod (ActualAffineScaling.modulus v.width))).val)%ActualAffineScaling.modulus v.width)
      (1288*volume prime v+186) := by
  apply (constructs_hoare r hs a hv hvpos).consequence (fun _ h => h) _ le_rfl
  rintro w rfl
  exact ⟨rfl,output_payload r hs a,fun x =>
    ⟨RecursiveInterchangeShift.array_entry r a x,RecursiveInterchangeShift.shiftAddress_d r hden x⟩⟩


end
end IntegerMultBounds.Machine.RecursiveInterchangeShiftConstruct
