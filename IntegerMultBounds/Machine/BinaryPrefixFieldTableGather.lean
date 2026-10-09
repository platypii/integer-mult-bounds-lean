import IntegerMultBounds.Machine.BinaryPrefixFieldTableSetup
import IntegerMultBounds.Machine.CountedGatherOriginalRun

/-! The actual runtime gather consumes the generated full-address table and
generated dummy stream. Six physical shape headers include a paid duplicate d
and a generated zero; all gather-private metadata is erased. -/
namespace IntegerMultBounds.Machine.BinaryPrefixFieldTableGather
noncomputable section
open SharedPlacementAlphabet (setTape)
open CompactGadgetReservationHeadersCore (bank)
open BinaryPrefixFieldTableSetup (prepared binary)
open BinaryPrefixFieldTableData (shape dummy word)
open RecursiveChildQuotientsConstant (bits)

def focus : Fin 9 → Fin 9 := ![5,6,7,0,1,2,8,4,3]
theorem focus_injective : Function.Injective focus := by decide

def headers (hs : Fin 3 → List Bool) (W : ℕ) : Fin 6 → List Bool :=
  ![hs 0,hs 1,hs 2,hs 2,bits 0,bits (2^W)]
def values (W start d : ℕ) : Fin 3 → ℕ := ![W,start,d]

def output (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W) :=
  setTape (setTape (setTape (prepared hs W) 5 (BinaryAddressTable.outputTape W) (2^W*W))
    6 (CountedCopyReuse.binary (dummy W)) (1+2^W)) 7
    (putWord (fun _ => blank) 0 ((word W start d h).map bitSymbol)) (2^W*d)

def program := extend (CountedGatherOriginalRun.program (a := 0) (fun x _ => x) focus focus_injective) 9

theorem header_values (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W)
    (hv : ∀ i, Counter.value (hs i)=values W start d i) :
    ∀ i, Counter.value (headers hs W i)=CountedGatherMetadata.originalValues (shape W start d h) (2^W) i := by
  intro i; fin_cases i <;> simp [headers,CountedGatherMetadata.originalValues,shape,hv,values,
    RecursiveChildQuotientsConstant.bits_value]

theorem header_canonical (hs : Fin 3 → List Bool) (W : ℕ)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (headers hs W i) := by
  intro i; fin_cases i <;> simp [headers,hc,RecursiveChildQuotientsConstant.bits_canonical]

theorem bank_eq (v : Tapes 9 0) :
    (CountedGatherOriginalRun.input v).append (SharedBank.empty 9 0)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem runs (hs : Fin 3 → List Bool) (W start d : ℕ) (h : start+d≤W)
    (hv : ∀ i, Counter.value (hs i)=values W start d i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime program (fun v => v=bank (prepared hs W))
      (fun v => v=bank (output hs W start d h)) (169*((2^W+1)*(W+d+1))) := by
  have hh := CountedGatherOriginalRun.runs (prepared hs W) focus focus_injective (fun x _ => x)
    (shape W start d h) (BinaryAddressTableData.table W (2^W)) (dummy W)
    (fun _ => blank) CountedCopyReuse.empty (fun _ => blank) 0 1 0 (headers hs W)
    (by simpa [dummy] using header_values hs W start d h hv) (header_canonical hs W hc)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
    rfl (BinaryAddressTableStep.bits_word _ _ _) rfl rfl rfl rfl
    (by simp [dummy,shape])
  have he : CountedGatherOriginalRun.result (prepared hs W) focus
      (putWord (fun _ => blank) 0 ((Gather.gather (fun x _ => x) (shape W start d h)
        (BinaryAddressTableData.table W (2^W)) (dummy W) (dummy W).length).map bitSymbol))
      (0+(dummy W).length*(shape W start d h).sx) (1+(dummy W).length)
      (0+(dummy W).length*(shape W start d h).st) = output hs W start d h := by
    simp only [dummy,List.length_replicate,shape,zero_add]
    rfl
  rw [he] at hh
  have hh' := hoare_extend_eq hh (SharedBank.empty 9 0)
  rw [bank_eq,bank_eq] at hh'
  refine hh'.consequence (fun _ h => h) (fun _ h => h) ?_
  simpa only [dummy,List.length_replicate,shape] using
    CountedGatherOriginalRun.cost_linear (shape W start d h) (2^W) (headers hs W)
      (header_values hs W start d h hv) (header_canonical hs W hc)

end
end IntegerMultBounds.Machine.BinaryPrefixFieldTableGather
