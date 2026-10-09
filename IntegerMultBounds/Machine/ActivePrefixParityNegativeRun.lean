import IntegerMultBounds.Machine.ActivePrefixParityNegativeBank

/-! Complete original-input production and rowwise negation. Header arithmetic,
positive offsets, negation, cleanup and every sequential join are paid. -/
namespace IntegerMultBounds.Machine.ActivePrefixParityNegativeRun
noncomputable section
open ActivePrefixParityOffsetBank (Shape values)
open ActivePrefixParityNegativeBank
variable {a : ℕ}

def bank (caller : Tapes 15 a) := CleanSubbank.bank (s := 41) caller
 theorem pad15 (caller : Tapes 15 a) :
    (CleanSubbank.bank (s := 15) caller).append (SharedBank.empty 26 a)=bank caller := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def positiveProgram := ActivePrefixParityOffsetPlaced.program (a := a) positiveFocus positive_injective
def headerProgram := extend (ActivePrefixOffsetHeadersRun.program (a := a) headerFocus header_injective) 26
def negateProgram := ActivePrefixParityNegativeNegate.program (a := a) negateFocus negate_injective
def cleanupProgram := extend (ActivePrefixOffsetHeadersCleanup.program (a := a)
  (ActivePrefixOffsetHeadersData.outputFocus headerFocus)) 41
def program := seq (seq (seq (positiveProgram (a := a)) headerProgram) negateProgram) cleanupProgram

def volume (s : Shape) := 2^s.W*(s.W+1)
def constant := ActivePrefixParityOffset.constant+ActivePrefixOffsetHeadersBudget.constant+167

 theorem compact_fits (s : Shape) : s.n*s.b≤s.W := by
  have h := Nat.mul_le_mul_left s.n (show s.b≤s.q by have := s.hbq; omega)
  have hT := s.tempFits
  omega

 theorem positive_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (positiveProgram (a := a)) (fun x => x=bank (base hs))
      (fun x => x=bank (positive s hs)) (ActivePrefixParityOffset.constant*volume s) :=
  ActivePrefixParityOffsetPlaced.produces _ _ positive_injective s hs (positive_sources hs) hv hc

 theorem header_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (headerProgram (a := a)) (fun x => x=bank (positive s hs))
      (fun x => x=bank (headers s hs)) (ActivePrefixOffsetHeadersBudget.constant*volume s) := by
  have h := ActivePrefixOffsetHeadersBudget.constructs (positive (a := a) s hs) headerFocus header_injective
    (originalWords hs) s.W s.q s.b s.n s.f (header_sources s hs)
    (by intro i; fin_cases i <;> first | exact hv 0 | exact hv 3 | exact hv 4 | exact hv 5 | exact hv 7)
    (by intro i; fin_cases i <;> first | exact hc 0 | exact hc 3 | exact hc 4 | exact hc 5 | exact hc 7)
    s.hb s.hbq s.hnf (by have := s.sourceFits; omega) (compact_fits s)
  simpa only [headerProgram,CompactGadgetReservationHeadersCore.bank,pad15,headers,ActivePrefixOffsetHeadersBudget.volume,volume] using
    hoare_extend_eq h (SharedBank.empty 26 a)

 theorem negate_runs (s : Shape) (hs : Fin 8 → List Bool) :
    HoareTime (negateProgram (a := a)) (fun x => x=bank (headers s hs))
      (fun x => x=bank (negated s hs)) (120*volume s) := by
  have h := ActivePrefixParityNegativeNegate.runs (headers (a := a) s hs) negateFocus negate_injective
    (ActivePrefixParityNegativeData.rows s) (s.n*s.b) (ActivePrefixParityNegativeData.rows_uniform s)
    (widthWord s) (countWord s) (RecursiveChildQuotientsConstant.bits_value _)
    (by rw [ActivePrefixParityNegativeData.rows_length]; exact RecursiveChildQuotientsConstant.bits_value _)
    (negate_sources s hs)
  have ht := BinaryParityXorOffsetNegate.cost_linear (s.n*s.b) (2^s.W) (widthWord s) (countWord s)
    (by positivity) (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
  have hf := Nat.mul_le_mul_left (2^s.W) (Nat.add_le_add_right (compact_fits s) 1)
  rw [ActivePrefixParityNegativeData.rows_length] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) (ht.trans (Nat.mul_le_mul_left 120 hf))

 theorem cleanup_runs (s : Shape) (hs : Fin 8 → List Bool) :
    HoareTime (cleanupProgram (a := a)) (fun x => x=bank (negated s hs))
      (fun x => x=bank (output s hs)) (44*volume s) := by
  have h := ActivePrefixOffsetHeadersCleanup.cleans (negated (a := a) s hs)
    (ActivePrefixOffsetHeadersData.outputFocus headerFocus)
    (ActivePrefixOffsetHeadersData.output_injective headerFocus header_injective)
    (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)
    (retained_headers s hs).1 (retained_headers s hs).2
  have ht := ActivePrefixOffsetHeadersCleanup.derived_cost s.W s.q s.b s.n s.f
    (by have := s.hbq; omega) s.hnf (by have := s.sourceFits; omega) (compact_fits s)
  exact (hoare_extend_eq h (SharedBank.empty 41 a)).consequence
    (fun _ h => h) (fun _ h => h) ht

 theorem runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun x => x=bank (base hs))
      (fun x => x=bank (output s hs)) (constant*volume s) := by
  have h := (((positive_runs (a := a) s hs hv hc).seq (header_runs (a := a) s hs hv hc)).seq (negate_runs (a := a) s hs)).seq (cleanup_runs (a := a) s hs)
  have hvol : 0<volume s := by unfold volume; positivity
  exact h.consequence (fun _ h => h) (fun _ h => h) (by unfold constant; nlinarith)

end
end IntegerMultBounds.Machine.ActivePrefixParityNegativeRun
