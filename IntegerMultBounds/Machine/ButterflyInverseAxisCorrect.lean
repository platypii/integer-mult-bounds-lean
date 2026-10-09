import IntegerMultBounds.Machine.ButterflyInverseAxisSemantics

/-! Combined literal-machine, complexity and inverse-kernel correctness for
runtime axis intervals. Every generated header and private tape is erased;
only original headers and the exact inverse-transformed stream survive. -/
namespace IntegerMultBounds.Machine.ButterflyInverseAxisCorrect
noncomputable section
open ButterflyAxisArray (Array Width)
open ButterflyAxisDecoded (decoded)
open ButterflyInverseAxisSemantics (directions decoded_walsh)
open Networks

/-- Negating all kernel signs in the same order is the actual inverse product:
all these translation kernels share the proved Walsh diagonalization. -/
theorem kernelRun_inverse {D : ℕ} (gs : List (ZMod 4 × BinaryWalsh.Address D))
    (f : BinaryWalsh.Arrays D) :
    BinaryWalsh.kernelRun (BinaryWalsh.negateKernels gs) (BinaryWalsh.kernelRun gs f)=f := by
  rw [BinaryWalsh.kernelRun_eq_frame,BinaryWalsh.kernelRun_eq_frame,
    BinaryWalsh.listPhase_negate,BinaryWalsh.frame_add,add_neg_cancel]
  exact BinaryWalsh.frame_zero f

/-- The actual fixed machine computes the claimed kernel sequence within the
paid linear-volume-per-axis budget, including runtime header construction. -/
theorem range_correct (D start R p n : ℕ) (hfit : start+n≤D) (hR : 0<R) (hn : 0<n)
    (f : Array D R) (hw : Width D R p f)
    (hunit : ∀ i, ‖ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1)
    (bs : List Bool) (hc : Counter.value bs=n) (hb : GrowingCounterData.Canonical bs) :
    HoareTime ButterflyInverseAxisSchedule.rangeProgram
      (fun v => v=ButterflyInverseAxisSchedule.rangeBank D start R p 0 f bs)
      (fun v => v=ButterflyInverseAxisSchedule.rangeBank D start R p n f bs ∧
        ∀ r : Fin R, (fun x => decoded D R p n (ButterflyInverseAxisSchedule.run D start R p n f)
          (FlatCoordinateLayout.index x r))=BinaryWalsh.kernelRun (directions D start n hfit)
            (fun x => decoded D R p 0 f (FlatCoordinateLayout.index x r)))
      (ButterflyInverseAxisSchedule.constant*ButterflyAxisHeadersBudget.logicalVolume D R p*n) :=
  (ButterflyInverseAxisSchedule.range_runs_linear D start R p n hfit hR hn f hw bs hc hb).consequence
    (fun _ h => h) (fun _ h => ⟨h,fun r => decoded_walsh D start R p n hfit f hw hunit r⟩) le_rfl

/-- The small-dimension fallback counts all axes directly from its original
D header and returns the exact full kernel product with all work tapes blank. -/
theorem all_correct (D R p : ℕ) (hD : 0<D) (hR : 0<R)
    (f : Array D R) (hw : Width D R p f)
    (hunit : ∀ i, ‖ButterflyStreamSemantics.decode (ButterflyGuard.halfWidth p D) p (f i)‖≤1) :
    HoareTime ButterflyInverseAxisSchedule.allProgram
      (fun v => v=ButterflyInverseAxisSchedule.allBank D R p 0 f)
      (fun v => v=ButterflyInverseAxisSchedule.allBank D R p D f ∧
        ∀ r : Fin R, (fun x => decoded D R p D (ButterflyInverseAxisSchedule.run D 0 R p D f)
          (FlatCoordinateLayout.index x r))=BinaryWalsh.kernelRun (directions D 0 D (by omega))
            (fun x => decoded D R p 0 f (FlatCoordinateLayout.index x r)))
      (ButterflyInverseAxisSchedule.constant*ButterflyAxisHeadersBudget.logicalVolume D R p*D) :=
  (ButterflyInverseAxisSchedule.all_runs_linear D R p hD hR f hw).consequence
    (fun _ h => h) (fun _ h => ⟨h,fun r => decoded_walsh D 0 R p D (by omega) f hw hunit r⟩) le_rfl


end
end IntegerMultBounds.Machine.ButterflyInverseAxisCorrect
