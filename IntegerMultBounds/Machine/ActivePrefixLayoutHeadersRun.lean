import IntegerMultBounds.Machine.ActivePrefixLayoutHeadersData

/-! Actual header preparation with a fixed 28+15 tape bank. A real constant
writer, retained-word arithmetic, power constructor and product constructor
prepare all ten consumer headers and erase their temporary words. -/
namespace IntegerMultBounds.Machine.ActivePrefixLayoutHeadersRun
noncomputable section
open ActivePrefixLayoutHeadersData ActiveRepairRankHeadersCommands
open RecursiveChildQuotientsConstant (bits)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def seedProgram := extend (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement (24 : Fin 28))) 15

def powerFocus : Fin 2 → Fin 28 := ![24,25]
def productFocus : Fin 3 → Fin 28 := ![25,13,23]
def powerProgram := CompactGadgetReservationHeadersPowerRound.powerProgram (a := a) powerFocus (by decide)
def productProgram := CompactGadgetReservationHeadersCore.productProgram (a := a) productFocus (by decide)
def program (mode : Mode) := seq (seq (seq (seq seedProgram (compile (a := a) (schedule mode)).2)
  powerProgram) productProgram) (compile (a := a) scratchCleanup).2

def cost (mode : Mode) (d : Inputs) := 9+scheduleCost (schedule mode) (seeded d)+
  FixedBasePowerDescriptor.constant 2*2^exponent mode d+(53*suffix mode d+28)+
  scheduleCost scratchCleanup (multiplied mode d)+4

theorem seed_runs (d : Inputs) :
    HoareTime (seedProgram (a := a)) (fun v => v=bank (initial d))
      (fun v => v=bank (seeded d)) 9 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement (24 : Fin 28)) (caller (a := a) (initial d))
    (by rw [FiniteReturnStackAt.active_bank]; simp [caller,initial])
  have h' : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
      (FiniteReturnStackAt.placement (24 : Fin 28))) (fun v => v=caller (initial d))
      (fun v => v=caller (seeded d)) 9 := by
    apply h.consequence (fun _ h => h) _ (by decide)
    rintro z ⟨small,rfl,rfl⟩
    rw [seeded,put_caller,FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact hoare_extend_eq h' (SharedBank.empty 15 a)

theorem arithmetic_runs (mode : Mode) (d : Inputs) (hw : d.w≤d.H) :
    HoareTime (compile (a := a) (schedule mode)).2 (fun v => v=bank (seeded d))
      (fun v => v=bank (arithmetic mode d)) (scheduleCost (schedule mode) (seeded d)) := by
  have h := schedule_runs (a := a) (schedule mode) (seeded d) (schedule_valid mode d hw)
  rwa [execute_eq] at h

theorem power_runs (mode : Mode) (d : Inputs) :
    HoareTime (powerProgram (a := a)) (fun v => v=bank (arithmetic mode d))
      (fun v => v=bank (powered mode d)) (FixedBasePowerDescriptor.constant 2*2^exponent mode d) := by
  have h := CompactGadgetReservationHeadersPowerRound.power (caller (a := a) (arithmetic mode d)) powerFocus (by decide)
    (bits (exponent mode d)) (exponent mode d) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _)
    (by simp [caller,arithmetic,powerFocus]) (by simp [caller,arithmetic,powerFocus])
    (by simp [caller,arithmetic,powerFocus]) (by simp [caller,arithmetic,powerFocus])
  simpa [powerProgram,powerFocus,powered,ActiveRepairRankHeadersCommands.bank,CompactGadgetReservationHeadersCore.bank,put_caller] using h

theorem product_runs (mode : Mode) (d : Inputs) :
    HoareTime (productProgram (a := a)) (fun v => v=bank (powered mode d))
      (fun v => v=bank (multiplied mode d)) (53*suffix mode d+28) := by
  have h := CompactGadgetReservationHeadersCore.product (caller (a := a) (powered mode d)) productFocus (by decide)
    (bits (2^exponent mode d)) (bits d.payload) d.payload (2^exponent mode d) (by positivity)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (by simp [caller,powered,put,productFocus,Function.update])
    (by simp [caller,powered,put,productFocus,Function.update])
    (by simp [caller,powered,put,arithmetic,originalValues,productFocus,Function.update])
    (by simp [caller,powered,put,arithmetic,productFocus,Function.update])
    (by simp [caller,powered,put,arithmetic,productFocus,Function.update])
    (by simp [caller,powered,put,arithmetic,productFocus,Function.update])
  simpa [productProgram,productFocus,multiplied,suffix,ActiveRepairRankHeadersCommands.bank,CompactGadgetReservationHeadersCore.bank,put_caller] using h

theorem runs (mode : Mode) (d : Inputs) (hw : d.w≤d.H) :
    HoareTime (program (a := a) mode) (fun v => v=bank (initial d))
      (fun v => v=bank (finished mode d)) (cost mode d) := by
  have he := schedule_runs (a := a) scratchCleanup (multiplied mode d) (scratch_valid mode d)
  rw [scratch_eq] at he
  exact ((((seed_runs d).seq (arithmetic_runs mode d hw)).seq (power_runs mode d)).seq (product_runs mode d)).seq he
    |>.consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

def cleanupProgram := (compile (a := a) outputCleanup).2
def cleanupCost (mode : Mode) (d : Inputs) := scheduleCost outputCleanup (finished mode d)

theorem cleans (mode : Mode) (d : Inputs) :
    HoareTime (cleanupProgram (a := a)) (fun v => v=bank (finished mode d))
      (fun v => v=bank (initial d)) (cleanupCost mode d) := by
  have h := schedule_runs (a := a) outputCleanup (finished mode d) (cleanup_valid mode d)
  rwa [cleanup_eq] at h

end
end IntegerMultBounds.Machine.ActivePrefixLayoutHeadersRun
