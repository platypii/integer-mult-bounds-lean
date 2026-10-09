import IntegerMultBounds.Machine.ButterflyInverseAxisCorrect

/-! Inverse execution can continue an existing arithmetic prefix. The machine
keeps its original guard-width header p, while the semantic precision begins at
p+j rather than requiring a fresh normalized input or free width conversion. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisContinuation
noncomputable section
open ButterflyAxisArray (Array Width)
open ButterflyAxisSemantics (Grid)
open ButterflyAxisDecoded (decoded)
open Networks

theorem grid_run (D start R p n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p j f) :
    Grid D R p (j+n) (ButterflyInverseAxisSchedule.run D start R p n f) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyInverseAxisSchedule.run,ButterflyInverseAxisSchedule.step,dite_eq_left ht]
    simpa only [Nat.add_assoc] using ButterflyInverseAxisArray.grid_apply D (start+n) R p (j+n) ht (by omega) _
      (ButterflyInverseAxisSchedule.width_run D start R p n f hw) (ih (by omega) (by omega))

theorem decoded_run (D start R p n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p j f) :
    decoded D R p (j+n) (ButterflyInverseAxisSchedule.run D start R p n f)=
      ButterflyInverseAxisSemantics.complexRun D start R p n (decoded D R p j f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht : start+n<D := by omega
    simp only [ButterflyInverseAxisSchedule.run,ButterflyInverseAxisSchedule.step,dite_eq_left ht,
      ButterflyInverseAxisSemantics.complexRun,ButterflyInverseAxisSemantics.complexStep]
    have hh := ButterflyInverseAxisArray.decoded_apply D (start+n) R p (j+n) ht (by omega) _
      (ButterflyInverseAxisSchedule.width_run D start R p n f hw)
      (grid_run D start R p n j (by omega) (by omega) f hw hg)
    rw [show j+(n+1)=j+n+1 by omega,hh,ih (by omega) (by omega)]

/-- Exact existing Walsh semantics without normalizing or resizing the input
between arithmetic phases. Only the remaining common guard budget is needed. -/
theorem decoded_walsh (D start R p n j : ℕ) (hfit : start+n≤D) (hguard : j+n≤D)
    (f : Array D R) (hw : Width D R p f) (hg : Grid D R p j f) (r : Fin R) :
    (fun x => decoded D R p (j+n) (ButterflyInverseAxisSchedule.run D start R p n f)
      (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (ButterflyInverseAxisSemantics.directions D start n hfit)
        (fun x => decoded D R p j f (FlatCoordinateLayout.index x r)) := by
  rw [decoded_run D start R p n j hfit hguard f hw hg]
  exact ButterflyInverseAxisSemantics.run_walsh D start R p n hfit _ r

end
end IntegerMultBounds.Machine.ButterflyInverseAxisContinuation
