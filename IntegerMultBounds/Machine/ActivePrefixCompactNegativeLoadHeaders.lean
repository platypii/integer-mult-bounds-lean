import IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoadData
import IntegerMultBounds.Machine.ActivePrefixOffsetHeadersCleanup

/-! Paid construction of P=rows times two-to-W and compact width n*b from
original descriptors, in the same blank workspace used by offset production. -/
namespace IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoadHeaders
noncomputable section
open ActivePrefixCompactNegativeLoadData
open ActivePrefixParityOffsetBank (Shape values)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def bank (v : Tapes 19 a) := CleanSubbank.bank (s := 56) v

theorem pad15 (v : Tapes 19 a) :
    (CompactGadgetReservationHeadersCore.bank v).append (SharedBank.empty 41 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def setup := extend (ActivePrefixOffsetHeadersRun.program (a := a) headerFocus header_injective) 41
def product := extend (CompactGadgetReservationHeadersCore.productProgram (a := a) productFocus product_injective) 41
def program := seq (setup (a := a)) (product (a := a))
def cost (s : Shape) (rows : ℕ) :=
  ActivePrefixOffsetHeadersBudget.constant*(2^s.W*(s.W+1))+53*prefixCount s rows+29

theorem setup_runs (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (setup (a := a))
      (fun v => v=bank (produced (base s rows B hs rs bs x) s))
      (fun v => v=bank (headers (base s rows B hs rs bs x) s))
      (ActivePrefixOffsetHeadersBudget.constant*(2^s.W*(s.W+1))) := by
  have h := ActivePrefixOffsetHeadersBudget.constructs (produced (base (a := a) s rows B hs rs bs x) s)
    headerFocus header_injective (headerWords hs) s.W s.q s.b s.n s.f
    (header_sources s rows B hs rs bs x)
    (by intro i; fin_cases i <;> first | exact hv 0 | exact hv 3 | exact hv 4 | exact hv 5 | exact hv 7)
    (by intro i; fin_cases i <;> first | exact hc 0 | exact hc 3 | exact hc 4 | exact hc 5 | exact hc 7)
    s.hb s.hbq s.hnf (by have := s.sourceFits; omega) (by have := s.tempFits; have hm := Nat.mul_le_mul_left s.n (show s.b≤s.q by have := s.hbq; omega); omega)
  simpa only [setup,pad15,headers,ActivePrefixOffsetHeadersBudget.volume] using
    hoare_extend_eq h (SharedBank.empty 41 a)

theorem product_runs (s : Shape) (rows B : ℕ) (hs : Fin 8 → List Bool) (rs bs : List Bool)
    (x : Array s rows B) (hv : Counter.value rs=rows)
    (hc : GrowingCounterData.Canonical rs) :
    HoareTime (product (a := a))
      (fun v => v=bank (headers (base s rows B hs rs bs x) s))
      (fun v => v=bank (dimensions (base s rows B hs rs bs x) s rows))
      (53*prefixCount s rows+28) := by
  have h := CompactGadgetReservationHeadersCore.product (headers (base (a := a) s rows B hs rs bs x) s)
    productFocus product_injective (bits (2^s.W)) rs rows (2^s.W) (by positivity)
    (RecursiveChildQuotientsConstant.bits_value _) hv (RecursiveChildQuotientsConstant.bits_canonical _) hc
    (by simp [headers,ActivePrefixOffsetHeadersData.result,ActivePrefixOffsetHeadersData.digitCount,
      ActivePrefixOffsetHeadersData.tempWidth,ActivePrefixOffsetHeadersData.sourceWidth,
      ActivePrefixOffsetHeadersData.power,ActivePrefixOffsetHeadersData.install,setTape,headerFocus,productFocus,Matrix.cons_val])
    (by simp [headers,ActivePrefixOffsetHeadersData.result,ActivePrefixOffsetHeadersData.digitCount,
      ActivePrefixOffsetHeadersData.tempWidth,ActivePrefixOffsetHeadersData.sourceWidth,
      ActivePrefixOffsetHeadersData.power,ActivePrefixOffsetHeadersData.install,setTape,headerFocus,productFocus,Matrix.cons_val])
    (by simp [headers,ActivePrefixOffsetHeadersData.result,ActivePrefixOffsetHeadersData.digitCount,
      ActivePrefixOffsetHeadersData.tempWidth,ActivePrefixOffsetHeadersData.sourceWidth,
      ActivePrefixOffsetHeadersData.power,ActivePrefixOffsetHeadersData.install,produced,
      ActivePrefixParityNegativePlaced.result,setTape,headerFocus,productFocus,producerFocus,base,Matrix.cons_val])
    (by simp [headers,ActivePrefixOffsetHeadersData.result,ActivePrefixOffsetHeadersData.digitCount,
      ActivePrefixOffsetHeadersData.tempWidth,ActivePrefixOffsetHeadersData.sourceWidth,
      ActivePrefixOffsetHeadersData.power,ActivePrefixOffsetHeadersData.install,produced,
      ActivePrefixParityNegativePlaced.result,setTape,headerFocus,productFocus,producerFocus,base,Matrix.cons_val])
    (by simp [headers,ActivePrefixOffsetHeadersData.result,ActivePrefixOffsetHeadersData.digitCount,
      ActivePrefixOffsetHeadersData.tempWidth,ActivePrefixOffsetHeadersData.sourceWidth,
      ActivePrefixOffsetHeadersData.power,ActivePrefixOffsetHeadersData.install,produced,
      ActivePrefixParityNegativePlaced.result,setTape,headerFocus,productFocus,producerFocus,base,Matrix.cons_val])
    (by simp [headers,ActivePrefixOffsetHeadersData.result,ActivePrefixOffsetHeadersData.digitCount,
      ActivePrefixOffsetHeadersData.tempWidth,ActivePrefixOffsetHeadersData.sourceWidth,
      ActivePrefixOffsetHeadersData.power,ActivePrefixOffsetHeadersData.install,produced,
      ActivePrefixParityNegativePlaced.result,setTape,headerFocus,productFocus,producerFocus,base,Matrix.cons_val])
  simpa only [product,pad15,dimensions,prefixCount,productFocus,Matrix.cons_val] using
    hoare_extend_eq h (SharedBank.empty 41 a)

end
end IntegerMultBounds.Machine.ActivePrefixCompactNegativeLoadHeaders
