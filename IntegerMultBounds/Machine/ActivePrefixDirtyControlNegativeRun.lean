import IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeBank

/-! Real dirty-U parity-XOR production and rowwise negation, including
physical width/count synthesis, source erasure, and complete metadata cleanup. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeRun
noncomputable section
open ActivePrefixDirtyControlData (Shape values)
open ActivePrefixDirtyControlNegativeData
open ActivePrefixDirtyControlNegativeBank
open RecursiveChildQuotientsConstant (bits)
variable {a : ℕ}

def bank (v : Tapes 10 a) := CleanSubbank.bank (s := 41) v

theorem pad15 (v : Tapes 10 a) :
    (CompactGadgetReservationHeadersCore.bank v).append (SharedBank.empty 26 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
theorem pad39 (v : Tapes 10 a) :
    (CleanSubbank.bank (s := 39) v).append (SharedBank.empty 2 a)=bank v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def makePositive := extend (ActivePrefixDirtyControlPlaced.program (a := a) .parity positiveFocus (by decide)) 2
def power := extend (CompactGadgetReservationHeadersPowerRound.powerProgram (a := a) powerFocus (by decide)) 26
def width := extend (CompactGadgetReservationHeadersCore.productProgram (a := a) widthFocus (by decide)) 26
def negate := ActivePrefixParityNegativeNegate.program (a := a) negateFocus (by decide)
def cleanupCore := seq (BinaryDescriptorCleanupList.oneProgram (a := a) (8 : Fin 10))
  (BinaryDescriptorCleanupList.oneProgram 9)
def cleanup := extend (cleanupCore (a := a)) 41

def program := seq (seq (seq (seq (makePositive (a := a)) power) width) negate) cleanup

def cleanupCost (s : Shape .parity) := 2*(bits (s.n*s.b)).length+2*(bits (2^s.W)).length+9
def cost (s : Shape .parity) := ActivePrefixDirtyControl.constant*ActivePrefixDirtyControl.volume s+
  FixedBasePowerDescriptor.constant 2*2^s.W+(53*(s.n*s.b)+28)+
  120*(2^s.W*(s.n*s.b+1))+cleanupCost s+4

theorem positive_runs (s : Shape .parity) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (makePositive (a := a)) (fun v => v=bank (base hs))
      (fun v => v=bank (positive s hs)) (ActivePrefixDirtyControl.constant*ActivePrefixDirtyControl.volume s) := by
  have h := ActivePrefixDirtyControlPlaced.produces (base (a := a) hs) positiveFocus (by decide) s hs
    (positive_sources hs) hv hc
  simpa only [makePositive,pad39,positive] using hoare_extend_eq h (SharedBank.empty 2 a)

theorem power_runs (s : Shape .parity) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (power (a := a)) (fun v => v=bank (positive s hs))
      (fun v => v=bank (powered s hs)) (FixedBasePowerDescriptor.constant 2*2^s.W) := by
  have h := CompactGadgetReservationHeadersPowerRound.power (positive (a := a) s hs) powerFocus (by decide)
    (hs 0) s.W (hv 0) (hc 0) rfl rfl rfl rfl
  simpa only [power,pad15,powered,show powerFocus 1=(9 : Fin 10) from rfl] using hoare_extend_eq h (SharedBank.empty 26 a)

theorem width_runs (s : Shape .parity) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (width (a := a)) (fun v => v=bank (powered s hs))
      (fun v => v=bank (headers s hs)) (53*(s.n*s.b)+28) := by
  have h := CompactGadgetReservationHeadersCore.product (powered (a := a) s hs) widthFocus (by decide)
    (hs 4) (hs 5) s.n s.b s.hb (hv 4) (hv 5) (hc 4) (hc 5)
    rfl rfl rfl rfl rfl rfl
  simpa only [width,pad15,headers,show widthFocus 2=(8 : Fin 10) from rfl] using hoare_extend_eq h (SharedBank.empty 26 a)

theorem negate_runs (s : Shape .parity) (hs : Fin 6 → List Bool) :
    HoareTime (negate (a := a)) (fun v => v=bank (headers s hs))
      (fun v => v=bank (negated s hs)) (120*(2^s.W*(s.n*s.b+1))) := by
  have h := ActivePrefixParityNegativeNegate.runs (headers (a := a) s hs) negateFocus (by decide)
    (rows s) (s.n*s.b) (rows_uniform s) (bits (s.n*s.b)) (bits (2^s.W))
    (RecursiveChildQuotientsConstant.bits_value _)
    (by rw [RecursiveChildQuotientsConstant.bits_value,rows_length]) (negate_sources s hs)
  have ht := BinaryParityXorOffsetNegate.cost_linear (s.n*s.b) (2^s.W) (bits (s.n*s.b)) (bits (2^s.W))
    (by positivity) (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [rows_length] at h
  exact h.consequence (fun _ h => h) (fun _ h => h) ht

theorem cleanup_runs (s : Shape .parity) (hs : Fin 6 → List Bool) :
    HoareTime (cleanup (a := a)) (fun v => v=bank (negated s hs))
      (fun v => v=bank (output s hs)) (cleanupCost s) := by
  have h₀ := BinaryDescriptorCleanupList.one_hoare (8 : Fin 10) (negated (a := a) s hs)
    (bits (s.n*s.b)) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h₁ := BinaryDescriptorCleanupList.one_hoare (9 : Fin 10) (widthCleared (a := a) s hs)
    (bits (2^s.W)) (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have h := (h₀.seq h₁).consequence (fun _ h => h) (fun _ h => h.trans (cleared s hs))
    (show _≤cleanupCost s from by unfold cleanupCost; omega)
  exact hoare_extend_eq h (SharedBank.empty 41 a)

theorem runs (s : Shape .parity) (hs : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=values s i) (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (program (a := a)) (fun v => v=bank (base hs)) (fun v => v=bank (output s hs)) (cost s) := by
  exact ((((positive_runs s hs hv hc).seq (power_runs s hs hv hc)).seq
    (width_runs s hs hv hc)).seq (negate_runs s hs)).seq (cleanup_runs s hs) |>.consequence
      (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlNegativeRun
