import IntegerMultBounds.Machine.ButterflyIndependentGuardSchedule
import IntegerMultBounds.Machine.ButterflyIndependentGuardBank

/-! One fixed machine reserves a two-pass signed guard, performs all forward
axes, physically resets its selected-axis descriptor, performs all inverse axes
and restores the original actual-precision header. The common stream starts
at the explicitly enlarged initial width; no free resizing occurs between
passes. The second pass consumes the first pass's actual grid and tape output. -/
namespace IntegerMultBounds.Machine.ButterflyIndependentGuardRoundtrip
noncomputable section
open ButterflyAxisArray (Array)
open ButterflyIndependentGuardHeaders (reservation)
open ButterflyIndependentGuardSemantics
open ButterflyStreamData (full)
open ButterflyIndependentGuardBank (bank)
open Networks

def forward (D R q : ℕ) (f : Array D R) := ButterflyAxisSchedule.run D 0 R (reservation D q) D f
def result (D R q : ℕ) (f : Array D R) := ButterflyInverseAxisSchedule.run D 0 R (reservation D q) D (forward D R q f)
def word {D R : ℕ} (f : Array D R) := full (fun _ => blank) 0 f

def program := seq (seq (seq (seq
  (ButterflyIndependentGuardBank.program ButterflyIndependentGuardHeaders.reserve)
  ButterflyAxisSchedule.allProgram)
  (ButterflyIndependentGuardBank.program ButterflyIndependentGuardHeaders.reset))
  ButterflyInverseAxisSchedule.allProgram)
  (ButterflyIndependentGuardBank.program ButterflyIndependentGuardHeaders.restore)

def volume (D R q : ℕ) := ButterflyAxisHeadersBudget.logicalVolume D R (reservation D q)
def constant := 2*ButterflyAxisSchedule.constant+3000

/-- Reserving both passes enlarges the serialized volume by at most a factor
two, so the extra guard preserves the established asymptotic volume bound. -/
theorem volume_le_two (D R q : ℕ) :
    volume D R q≤2*ButterflyAxisHeadersBudget.logicalVolume D R q := by
  have hr : ButterflyAxisHeadersData.recordLength D (reservation D q)≤
      2*ButterflyAxisHeadersData.recordLength D q := by
    unfold ButterflyAxisHeadersData.recordLength ButterflyAxisHeadersData.width reservation
    omega
  have hh := Nat.mul_le_mul_left (2^D*R) hr
  unfold volume ButterflyAxisHeadersBudget.logicalVolume
  nlinarith

theorem forward_runs (D R q : ℕ) (hD : 0<D) (hR : 0<R) (f : Array D R) (hw : Width D R q f) :
    HoareTime ButterflyAxisSchedule.allProgram
      (fun v => v=bank D 0 R (reservation D q) (word f))
      (fun v => v=bank D D R (reservation D q) (word (forward D R q f)))
      (ButterflyAxisSchedule.constant*volume D R q*D) := by
  have hh := ButterflyAxisSchedule.all_runs_linear D R (reservation D q) hD hR f hw
  simpa only [ButterflyAxisSchedule.allBank,ButterflyAxisSchedule.endpoint,ButterflyAxisSchedule.run,
    Nat.zero_add,bank,word,forward,volume] using hh

theorem inverse_runs (D R q : ℕ) (hD : 0<D) (hR : 0<R) (f : Array D R) (hw : Width D R q f) :
    HoareTime ButterflyInverseAxisSchedule.allProgram
      (fun v => v=bank D 0 R (reservation D q) (word (forward D R q f)))
      (fun v => v=bank D D R (reservation D q) (word (result D R q f)))
      (ButterflyAxisSchedule.constant*volume D R q*D) := by
  have hh := ButterflyInverseAxisSchedule.all_runs_linear D R (reservation D q) hD hR (forward D R q f)
    (ButterflyAxisSchedule.width_run D 0 R (reservation D q) D f hw)
  simpa only [ButterflyInverseAxisSchedule.allBank,ButterflyInverseAxisSchedule.endpoint,ButterflyInverseAxisSchedule.run,
    Nat.zero_add,bank,word,result,volume,ButterflyInverseAxisSchedule.constant,ButterflyAxisSchedule.constant] using hh

theorem runs (D R q : ℕ) (hD : 0<D) (hR : 0<R) (f : Array D R) (hw : Width D R q f) :
    HoareTime program (fun v => v=bank D 0 R q (word f))
      (fun v => v=bank D D R q (word (result D R q f))) (constant*volume D R q*D) := by
  have h0 := ButterflyIndependentGuardBank.reserves D 0 R q (word f)
  have h1 := forward_runs D R q hD hR f hw
  have h2 := ButterflyIndependentGuardBank.resets D D R (reservation D q) (word (forward D R q f))
  have h3 := inverse_runs D R q hD hR f hw
  have h4 := ButterflyIndependentGuardBank.restores D D R q (word (result D R q f))
  have hV := ButterflyAxisHeadersInstall.volume_pos D R (reservation D q) hR
  have hv := ButterflyAxisHeadersBudget.values_le D 0 R (reservation D q) hD hR
  have hdim := hv.1
  have hp := hv.2.1
  have hm : volume D R q≤volume D R q*D := Nat.le_mul_of_pos_right _ hD
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence (fun _ h => h) (fun _ h => h) (by
    change 0<volume D R q at hV
    change D≤volume D R q at hdim
    change reservation D q≤volume D R q at hp
    unfold constant
    nlinarith)

/-- The first pass establishes precisely the enlarged-budget grid consumed by
the second; inverse input is never assumed freshly normalized. -/
theorem forward_grid (D R q : ℕ) (f : Array D R) (hw : Width D R q f)
    (hu : ∀ i,‖decoded D R q 0 f i‖≤1) : Grid D R q D (forward D R q f) := by
  have hh := ButterflyIndependentGuardSchedule.forward_grid_run D 0 R q D 0 (by omega) (by omega)
    f hw (initial_grid D R q f hu)
  simpa only [Nat.zero_add,forward] using hh

theorem result_grid (D R q : ℕ) (f : Array D R) (hw : Width D R q f)
    (hu : ∀ i,‖decoded D R q 0 f i‖≤1) : Grid D R q (2*D) (result D R q f) := by
  have hh := ButterflyIndependentGuardSchedule.inverse_grid_run D 0 R q D D (by omega) (by omega)
    (forward D R q f) (ButterflyAxisSchedule.width_run D 0 R (reservation D q) D f hw)
    (forward_grid D R q f hw hu)
  simpa only [←two_mul,result] using hh

/-- The literal forward-then-inverse stream decodes exactly to its original
values at final precision q+2D, on the repository's common coordinate layout. -/
theorem decoded_result (D R q : ℕ) (f : Array D R) (hw : Width D R q f)
    (hu : ∀ i,‖decoded D R q 0 f i‖≤1) (r : Fin R) :
    (fun x => decoded D R q (2*D) (result D R q f) (FlatCoordinateLayout.index x r))=
      (fun x => decoded D R q 0 f (FlatCoordinateLayout.index x r)) := by
  have hf := ButterflyIndependentGuardSchedule.forward_walsh D 0 R q D 0 (by omega) (by omega)
    f hw (initial_grid D R q f hu) r
  simp only [Nat.zero_add] at hf
  change (fun x => decoded D R q D (forward D R q f) (FlatCoordinateLayout.index x r))=_ at hf
  have hi := ButterflyIndependentGuardSchedule.inverse_walsh D 0 R q D D (by omega) (by omega)
    (forward D R q f) (ButterflyAxisSchedule.width_run D 0 R (reservation D q) D f hw)
    (forward_grid D R q f hw hu) r
  change (fun x => decoded D R q (D+D) (result D R q f) (FlatCoordinateLayout.index x r))=
    BinaryWalsh.kernelRun (BinaryWalsh.negateKernels (ButterflyAxisWalsh.directions D 0 D (by omega)))
      (fun x => decoded D R q D (forward D R q f) (FlatCoordinateLayout.index x r)) at hi
  rw [hf,ButterflyInverseAxisCorrect.kernelRun_inverse] at hi
  simpa only [←two_mul] using hi

theorem correct (D R q : ℕ) (hD : 0<D) (hR : 0<R) (f : Array D R) (hw : Width D R q f)
    (hu : ∀ i,‖decoded D R q 0 f i‖≤1) :
    HoareTime program (fun v => v=bank D 0 R q (word f))
      (fun v => v=bank D D R q (word (result D R q f)) ∧
        ∀ r : Fin R,(fun x => decoded D R q (2*D) (result D R q f) (FlatCoordinateLayout.index x r))=
          (fun x => decoded D R q 0 f (FlatCoordinateLayout.index x r)))
      (constant*volume D R q*D) :=
  (runs D R q hD hR f hw).consequence (fun _ h => h)
    (fun _ h => ⟨h,fun r => decoded_result D R q f hw hu r⟩) le_rfl

end
end IntegerMultBounds.Machine.ButterflyIndependentGuardRoundtrip
