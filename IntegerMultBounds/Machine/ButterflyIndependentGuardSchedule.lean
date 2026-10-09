import IntegerMultBounds.Machine.ButterflyIndependentGuardSemantics

/-! A shared independent guard validates consecutive forward and inverse runs
at their real accrued precisions. No normalization hypothesis is reintroduced
between phases; the prior phase's proved grid is the next phase's input. -/
namespace IntegerMultBounds.Machine.ButterflyIndependentGuardSchedule
noncomputable section
open ButterflyAxisArray (Array)
open ButterflyIndependentGuardHeaders (reservation)
open ButterflyIndependentGuardSemantics
open Networks

theorem forward_grid_run (D start R q n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) :
    Grid D R q (j+n) (ButterflyAxisSchedule.run D start R (reservation D q) n f) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyAxisSchedule.run,ButterflyAxisSchedule.step,dite_eq_left ht]
    simpa only [Nat.add_assoc] using forward_grid D (start+n) R q (j+n) ht (by omega) _
      (ButterflyAxisSchedule.width_run D start R (reservation D q) n f hw) (ih (by omega) (by omega))

theorem forward_decoded_run (D start R q n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) :
    decoded D R q (j+n) (ButterflyAxisSchedule.run D start R (reservation D q) n f)=
      ButterflyAxisDecoded.complexRun D start R (reservation D q) n (decoded D R q j f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyAxisSchedule.run,ButterflyAxisSchedule.step,dite_eq_left ht,
      ButterflyAxisDecoded.complexRun,ButterflyAxisDecoded.complexStep]
    have hh := forward_decoded D (start+n) R q (j+n) ht (by omega) _
      (ButterflyAxisSchedule.width_run D start R (reservation D q) n f hw)
      (forward_grid_run D start R q n j (by omega) (by omega) f hw hg)
    rw [show j+(n+1)=j+n+1 by omega,hh,ih (by omega) (by omega)]

theorem forward_walsh (D start R q n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) (r : Fin R) :
    (fun x => decoded D R q (j+n) (ButterflyAxisSchedule.run D start R (reservation D q) n f)
      (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (ButterflyAxisWalsh.directions D start n hfit)
        (fun x => decoded D R q j f (FlatCoordinateLayout.index x r)) := by
  rw [forward_decoded_run D start R q n j hfit hguard f hw hg]
  exact ButterflyAxisWalsh.run_walsh D start R (reservation D q) n hfit _ r

theorem inverse_grid_run (D start R q n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) :
    Grid D R q (j+n) (ButterflyInverseAxisSchedule.run D start R (reservation D q) n f) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyInverseAxisSchedule.run,ButterflyInverseAxisSchedule.step,dite_eq_left ht]
    simpa only [Nat.add_assoc] using inverse_grid D (start+n) R q (j+n) ht (by omega) _
      (ButterflyInverseAxisSchedule.width_run D start R (reservation D q) n f hw) (ih (by omega) (by omega))

theorem inverse_decoded_run (D start R q n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) :
    decoded D R q (j+n) (ButterflyInverseAxisSchedule.run D start R (reservation D q) n f)=
      ButterflyInverseAxisSemantics.complexRun D start R (reservation D q) n (decoded D R q j f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyInverseAxisSchedule.run,ButterflyInverseAxisSchedule.step,dite_eq_left ht,
      ButterflyInverseAxisSemantics.complexRun,ButterflyInverseAxisSemantics.complexStep]
    have hh := inverse_decoded D (start+n) R q (j+n) ht (by omega) _
      (ButterflyInverseAxisSchedule.width_run D start R (reservation D q) n f hw)
      (inverse_grid_run D start R q n j (by omega) (by omega) f hw hg)
    rw [show j+(n+1)=j+n+1 by omega,hh,ih (by omega) (by omega)]

theorem inverse_walsh (D start R q n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤2*D)
    (f : Array D R) (hw : Width D R q f) (hg : Grid D R q j f) (r : Fin R) :
    (fun x => decoded D R q (j+n) (ButterflyInverseAxisSchedule.run D start R (reservation D q) n f)
      (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (ButterflyInverseAxisSemantics.directions D start n hfit)
        (fun x => decoded D R q j f (FlatCoordinateLayout.index x r)) := by
  rw [inverse_decoded_run D start R q n j hfit hguard f hw hg]
  exact ButterflyInverseAxisSemantics.run_walsh D start R (reservation D q) n hfit _ r

end
end IntegerMultBounds.Machine.ButterflyIndependentGuardSchedule
