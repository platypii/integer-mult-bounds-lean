import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersRun

/-! The actual forward record formatter's count is generated from original
rows and the derived address exponent. No full record count is supplied. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersCount
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairRankHeadersCommands ActiveRepairLayoutRecordsHeadersSchedule
open ActiveRepairLayoutRecordsHeadersData
open RecursiveChildQuotientsConstant (bits)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ} {a : ℕ}

def exponent (d : Inputs s p offset rows) := put (finished d) 20 s.bits
def powered (d : Inputs s p offset rows) := put (exponent d) 21 (2^s.bits)
def counted (d : Inputs s p offset rows) := put (powered d) 19 (rows*2^s.bits)
def ready (d : Inputs s p offset rows) := put (finished d) 19 (rows*2^s.bits)
def difference : Command := .difference 18 14 20 (by decide)
def powerFocus : Fin 2 → Fin 28 := ![20,21]
def productFocus : Fin 3 → Fin 28 := ![21,12,19]
def cleanup : List Command := [.erase 20,.erase 21]
def differenceProgram := (one (a := a) difference).2
def powerProgram := CompactGadgetReservationHeadersPowerRound.powerProgram (a := a) powerFocus (by decide)
def productProgram := CompactGadgetReservationHeadersCore.productProgram (a := a) productFocus (by decide)
def cleanupProgram := (compile (a := a) cleanup).2
def program := seq (seq (seq (seq (ActiveRepairLayoutRecordsHeadersRun.program (a := a))
  (differenceProgram (a := a))) (powerProgram (a := a))) (productProgram (a := a))) (cleanupProgram (a := a))

theorem difference_runs (d : Inputs s p offset rows) :
    HoareTime (differenceProgram (a := a)) (fun v => v=bank (finished d))
      (fun v => v=bank (exponent d)) (cost difference (finished d)) := by
  have hv : ActiveRepairRankHeadersCommands.valid difference (finished d) := by
    simp [ActiveRepairRankHeadersCommands.valid,difference,finished,scanned,put,Function.update,initial]
  have hh := runs (a := a) difference (finished d) hv
  have he : eval difference (finished d)=exponent d := by
    simp [eval,difference,finished,scanned,put,Function.update,exponent]
  rwa [he] at hh

theorem power_runs (d : Inputs s p offset rows) :
    HoareTime (powerProgram (a := a)) (fun v => v=bank (exponent d))
      (fun v => v=bank (powered d)) (FixedBasePowerDescriptor.constant 2*2^s.bits) := by
  have h := CompactGadgetReservationHeadersPowerRound.power (caller (a := a) (exponent d)) powerFocus (by decide)
    (bits s.bits) s.bits (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _)
    (by simp [caller,exponent,put,powerFocus,Function.update]) (by simp [caller,exponent,put,powerFocus,Function.update])
    (by simp [caller,exponent,finished,scanned,initial,put,powerFocus,Function.update])
    (by simp [caller,exponent,finished,scanned,initial,put,powerFocus,Function.update])
  simpa [powerProgram,powerFocus,powered,bank,CompactGadgetReservationHeadersCore.bank,put_caller] using h

theorem product_runs (d : Inputs s p offset rows) :
    HoareTime (productProgram (a := a)) (fun v => v=bank (powered d))
      (fun v => v=bank (counted d)) (53*(rows*2^s.bits)+28) := by
  have h := CompactGadgetReservationHeadersCore.product (caller (a := a) (powered d)) productFocus (by decide)
    (bits (2^s.bits)) (bits rows) rows (2^s.bits) (by positivity)
    (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_value _)
    (RecursiveChildQuotientsConstant.bits_canonical _) (RecursiveChildQuotientsConstant.bits_canonical _)
    (by simp [caller,powered,put,productFocus,Function.update]) (by simp [caller,powered,put,productFocus,Function.update])
    (by simp [caller,powered,exponent,finished,scanned,initial,put,productFocus,Function.update,
      ActivePrefixLayoutHeadersData.originalValues,ActivePrefixLayoutHeadersGeometry.inputs])
    (by simp [caller,powered,exponent,finished,scanned,initial,put,productFocus,Function.update,
      ActivePrefixLayoutHeadersData.originalValues,ActivePrefixLayoutHeadersGeometry.inputs])
    (by simp [caller,powered,exponent,finished,scanned,initial,put,productFocus,Function.update])
    (by simp [caller,powered,exponent,finished,scanned,initial,put,productFocus,Function.update])
  simpa [productProgram,productFocus,counted,bank,CompactGadgetReservationHeadersCore.bank,
    put_caller,Nat.mul_comm] using h

theorem cleanup_runs (d : Inputs s p offset rows) :
    HoareTime (cleanupProgram (a := a)) (fun v => v=bank (counted d))
      (fun v => v=bank (ready d)) (scheduleCost cleanup (counted d)) := by
  have hv : validSchedule cleanup (counted d) := by
    simp [cleanup,validSchedule,ActiveRepairRankHeadersCommands.valid,eval,counted,powered,exponent,finished,scanned,put,Function.update]
  have he : execute cleanup (counted d)=ready d := by
    funext i
    fin_cases i <;> simp [cleanup,execute,eval,counted,powered,exponent,finished,scanned,put,Function.update,initial,ready]
  have h := schedule_runs (a := a) cleanup (counted d) hv
  rwa [he] at h

def runtime (d : Inputs s p offset rows) := ActiveRepairLayoutRecordsHeadersRun.cost d+
  cost difference (finished d)+FixedBasePowerDescriptor.constant 2*2^s.bits+53*(rows*2^s.bits)+28+
  scheduleCost cleanup (counted d)+4

theorem prepares (d : Inputs s p offset rows) :
    HoareTime (program (a := a)) (fun v => v=bank (initial d))
      (fun v => v=bank (ready d)) (runtime d) := by
  exact (((((ActiveRepairLayoutRecordsHeadersRun.runs d).seq (difference_runs d)).seq
    (power_runs d)).seq (product_runs d)).seq (cleanup_runs d)).consequence
    (fun _ hv => hv) (fun _ hv => hv) (by unfold runtime; omega)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersCount
