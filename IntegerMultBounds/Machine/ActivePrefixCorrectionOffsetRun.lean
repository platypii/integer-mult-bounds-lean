import IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetBank

/-! Actual complete producers and rowwise modular subtraction share forty-one
blank private tapes. Operand tables and derived descriptors are erased before
return; no operand or derived dimension is supplied by the caller. -/
namespace IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetRun
noncomputable section
open ActivePrefixCorrectionOffsetBank
open ActivePrefixSelectedOffsetBank (Shape values headerWords)
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def bank (v : Tapes 16 a) := CleanSubbank.bank (s := 41) v

theorem pad15 (v : Tapes 16 a) :
    (CompactGadgetReservationHeadersCore.bank v).append (SharedBank.empty 26 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
theorem pad9 (v : Tapes 16 a) :
    (CleanSubbank.bank (s := 9) v).append (SharedBank.empty 32 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def makeSelected := ActivePrefixSelectedOffsetPlaced.program (a := a) selectedFocus selected_injective
def makeControl := ActivePrefixControlOffsetPlaced.program (a := a) controlFocus control_injective
def setup := extend (ActivePrefixOffsetHeadersRun.program (a := a) headerFocus header_injective) 26
def subtract := extend (ActivePrefixCorrectionOffsetSubtract.program (a := a) subtractFocus subtract_injective) 32
def cleanup := extend (ActivePrefixOffsetHeadersCleanup.program (a := a) cleanupFocus) 41

def program := seq (seq (seq (seq (makeSelected (a := a)) makeControl) setup) subtract) cleanup

def cost (s : Shape) := ActivePrefixSelectedOffset.constant*(2^s.W*(s.W+1))+
  ActivePrefixControlOffset.constant*(2^s.W*(s.W+1))+
  ActivePrefixOffsetHeadersBudget.constant*(2^s.W*(s.W+1))+
  160*(2^s.W*(s.n*s.q+1))+
  ActivePrefixOffsetHeadersCleanup.cost (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)+4

theorem selected_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (makeSelected (a := a)) (fun v => v=bank (base hs))
      (fun v => v=bank (selectedReady s hs)) (ActivePrefixSelectedOffset.constant*(2^s.W*(s.W+1))) :=
  ActivePrefixSelectedOffsetPlaced.produces _ _ selected_injective s hs (selected_sources hs) hv hc

theorem control_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (makeControl (a := a)) (fun v => v=bank (selectedReady s hs))
      (fun v => v=bank (operands s hs)) (ActivePrefixControlOffset.constant*(2^s.W*(s.W+1))) :=
  ActivePrefixControlOffsetPlaced.produces _ _ control_injective s hs (control_sources s hs) hv hc

theorem setup_runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (setup (a := a)) (fun v => v=bank (operands s hs))
      (fun v => v=bank (headers s hs)) (ActivePrefixOffsetHeadersBudget.constant*(2^s.W*(s.W+1))) := by
  have h := ActivePrefixOffsetHeadersBudget.constructs (operands (a := a) s hs) headerFocus header_injective
    (headerWords hs) s.W s.q s.b s.n s.f (header_sources s hs)
    (by intro i; fin_cases i <;> first | exact hv 0 | exact hv 3 | exact hv 4 | exact hv 5 | exact hv 7)
    (by intro i; fin_cases i <;> first | exact hc 0 | exact hc 3 | exact hc 4 | exact hc 5 | exact hc 7)
    s.hb s.hbq s.hnf (by have := s.sourceFits; omega) (by have := s.tempFits; omega)
  simpa only [setup,pad15,headers,ActivePrefixOffsetHeadersBudget.volume] using
    hoare_extend_eq h (SharedBank.empty 26 a)

theorem subtract_runs (s : Shape) (hs : Fin 8 → List Bool) :
    HoareTime (subtract (a := a)) (fun v => v=bank (headers s hs))
      (fun v => v=bank (subtracted s hs)) (160*(2^s.W*(s.n*s.q+1))) := by
  have h := ActivePrefixCorrectionOffsetSubtract.runs (headers (a := a) s hs) subtractFocus subtract_injective
    (ActivePrefixCorrectionOffsetData.rows s) (s.n*s.q) (ActivePrefixCorrectionOffsetData.uniform s)
    (bits (s.n*s.q)) (bits (2^s.W)) (RecursiveChildQuotientsConstant.bits_value _)
    (by rw [RecursiveChildQuotientsConstant.bits_value,ActivePrefixCorrectionOffsetData.rows_length])
    (by rw [ActivePrefixCorrectionOffsetData.rows_length]; positivity)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (subtract_sources s hs)
  simpa only [subtract,pad9,subtracted,ActivePrefixCorrectionOffsetData.word,
    ActivePrefixCorrectionOffsetData.rows_length] using hoare_extend_eq h (SharedBank.empty 32 a)

theorem cleanup_runs (s : Shape) (hs : Fin 8 → List Bool) :
    HoareTime (cleanup (a := a)) (fun v => v=bank (subtracted s hs))
      (fun v => v=bank (output s hs))
      (ActivePrefixOffsetHeadersCleanup.cost (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)) := by
  have h := ActivePrefixOffsetHeadersCleanup.cleans (subtracted (a := a) s hs) cleanupFocus cleanup_injective
    _ (cleanup_tapes s hs).1 (cleanup_tapes s hs).2
  rw [cleared] at h
  exact hoare_extend_eq h (SharedBank.empty 41 a)

theorem runs (s : Shape) (hs : Fin 8 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=bank (base hs))
      (fun v => v=bank (output s hs)) (cost s) := by
  exact ((((selected_runs s hs hv hc).seq (control_runs s hs hv hc)).seq (setup_runs s hs hv hc)).seq
    (subtract_runs s hs)).seq (cleanup_runs s hs) |>.consequence
      (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixCorrectionOffsetRun
