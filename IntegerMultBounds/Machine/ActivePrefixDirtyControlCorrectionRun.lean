import IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionBank

/-! Correction executes the dirty-U selected and control producers, constructs
row width/count, subtracts with a fresh borrow for every row, and erases headers.
Both operand streams are consumed by the real subtraction machine. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionRun
noncomputable section
open ActivePrefixDirtyControlData (Shape values)
open ActivePrefixDirtyControlCorrectionData
open ActivePrefixDirtyControlCorrectionBank
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def bank (v : Tapes 11 a) := CleanSubbank.bank (s := 39) v

theorem pad15 (v : Tapes 11 a) :
    (CompactGadgetReservationHeadersCore.bank v).append (SharedBank.empty 24 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
theorem pad9 (v : Tapes 11 a) :
    (CleanSubbank.bank (s := 9) v).append (SharedBank.empty 30 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def makeSelected := ActivePrefixDirtyControlPlaced.program (a := a) .selected selectedFocus (by decide)
def makeControl := ActivePrefixDirtyControlPlaced.program (a := a) .control controlFocus (by decide)
def power := extend (CompactGadgetReservationHeadersPowerRound.powerProgram (a := a) powerFocus (by decide)) 24
def width := extend (CompactGadgetReservationHeadersCore.productProgram (a := a) widthFocus (by decide)) 24
def subtract := extend (ActivePrefixCorrectionOffsetSubtract.program (a := a) subtractFocus (by decide)) 30
def cleanupCore := seq (BinaryDescriptorCleanupList.oneProgram (a := a) (9 : Fin 11))
  (BinaryDescriptorCleanupList.oneProgram 10)
def cleanup := extend (cleanupCore (a := a)) 39

def program := seq (seq (seq (seq (seq (makeSelected (a := a)) makeControl) power) width) subtract) cleanup

def cleanupCost (s : Shape .selected) := 2*(bits (s.n*s.q)).length+2*(bits (2^s.W)).length+9
def cost (s : Shape .selected) := 2*(ActivePrefixDirtyControl.constant*ActivePrefixDirtyControl.volume s)+
  FixedBasePowerDescriptor.constant 2*2^s.W+(53*(s.n*s.q)+28)+
  160*(2^s.W*(s.n*s.q+1))+cleanupCost s+5

theorem selected_runs (s : Shape .selected) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (makeSelected (a := a)) (fun v => v=bank (base hs))
      (fun v => v=bank (selectedReady s hs)) (ActivePrefixDirtyControl.constant*ActivePrefixDirtyControl.volume s) :=
  ActivePrefixDirtyControlPlaced.produces _ _ (by decide) s hs (selected_sources hs) hv hc

theorem control_runs (s : Shape .selected) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (makeControl (a := a)) (fun v => v=bank (selectedReady s hs))
      (fun v => v=bank (operands s hs)) (ActivePrefixDirtyControl.constant*ActivePrefixDirtyControl.volume s) :=
  ActivePrefixDirtyControlPlaced.produces _ _ (by decide) (controlShape s) hs (control_sources s hs) hv hc

theorem power_runs (s : Shape .selected) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (power (a := a)) (fun v => v=bank (operands s hs))
      (fun v => v=bank (powered s hs)) (FixedBasePowerDescriptor.constant 2*2^s.W) := by
  have h := CompactGadgetReservationHeadersPowerRound.power (operands (a := a) s hs) powerFocus (by decide)
    (hs 0) s.W (hv 0) (hc 0) rfl rfl rfl rfl
  simpa only [power,pad15,powered,show powerFocus 1=(10 : Fin 11) from rfl] using hoare_extend_eq h (SharedBank.empty 24 a)

theorem width_runs (s : Shape .selected) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (width (a := a)) (fun v => v=bank (powered s hs))
      (fun v => v=bank (headers s hs)) (53*(s.n*s.q)+28) := by
  have h := CompactGadgetReservationHeadersCore.product (powered (a := a) s hs) widthFocus (by decide)
    (hs 3) (hs 5) s.n s.q (by have := s.hbq; omega) (hv 3) (hv 5) (hc 3) (hc 5)
    rfl rfl rfl rfl rfl rfl
  simpa only [width,pad15,headers,show widthFocus 2=(9 : Fin 11) from rfl] using hoare_extend_eq h (SharedBank.empty 24 a)

theorem subtract_runs (s : Shape .selected) (hs : Fin 6 → List Bool) :
    HoareTime (subtract (a := a)) (fun v => v=bank (headers s hs))
      (fun v => v=bank (subtracted s hs)) (160*(2^s.W*(s.n*s.q+1))) := by
  have h := ActivePrefixCorrectionOffsetSubtract.runs (headers (a := a) s hs) subtractFocus (by decide)
    (rows s) (s.n*s.q) (uniform s) (bits (s.n*s.q)) (bits (2^s.W))
    (RecursiveChildQuotientsConstant.bits_value _)
    (by rw [RecursiveChildQuotientsConstant.bits_value,rows_length]) (by rw [rows_length]; positivity)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (subtract_sources s hs)
  simpa only [subtract,pad9,subtracted,word,rows_length] using hoare_extend_eq h (SharedBank.empty 30 a)

theorem cleanup_runs (s : Shape .selected) (hs : Fin 6 → List Bool) :
    HoareTime (cleanup (a := a)) (fun v => v=bank (subtracted s hs))
      (fun v => v=bank (output s hs)) (cleanupCost s) := by
  have h₀ := BinaryDescriptorCleanupList.one_hoare (9 : Fin 11) (subtracted (a := a) s hs)
    (bits (s.n*s.q)) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h₁ := BinaryDescriptorCleanupList.one_hoare (10 : Fin 11) (widthCleared (a := a) s hs)
    (bits (2^s.W)) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h := (h₀.seq h₁).consequence (fun _ h => h) (fun _ h => h.trans (cleared s hs))
    (show _≤cleanupCost s from by unfold cleanupCost; omega)
  exact hoare_extend_eq h (SharedBank.empty 39 a)

theorem runs (s : Shape .selected) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=bank (base hs)) (fun v => v=bank (output s hs)) (cost s) := by
  exact (((((selected_runs s hs hv hc).seq (control_runs s hs hv hc)).seq (power_runs s hs hv hc)).seq
    (width_runs s hs hv hc)).seq (subtract_runs s hs)).seq (cleanup_runs s hs) |>.consequence
      (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlCorrectionRun
