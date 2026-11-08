module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryRows

/-! The second-pass and assembly queues read solved boundary rows and original
RHS in the same order. Prove this once for an arbitrary row interpretation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s : ℕ} [NeZero s]

theorem cyclicBoundaryRecoveryRows_map_read {β : Type} (f : CyclicRecoveryRow s → β) (default : β)
    (B : Finset (ZMod s)) (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hlen : solutions.length = Fs.length) (j : Fin Fs.length) :
    ((cyclicBoundaryRecoveryRows B solutions Fs).map f).reverse.getD j.val default =
      f (boundarySolutionField B (solutions.getD j.val []),
        (Fs.getD j.val (fun _ => 0),Fs.getD j.val (fun _ => 0))) := by
  simp only [cyclicBoundaryRecoveryRows,List.map_map,←List.map_reverse,List.reverse_reverse]
  have hzip : j.val < (solutions.zip Fs).length := by
    simpa only [List.length_zip,hlen,Nat.min_self] using j.isLt
  have hsol : j.val < solutions.length := by simpa only [hlen] using j.isLt
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hzip),List.getElem_map,
    List.getElem_zip,List.getD_eq_getElem _ _ hsol,List.getD_eq_getElem _ _ j.isLt]
  rfl

theorem cyclicReplica_rhs_read (Fs : List (ZMod s → GaussianInt)) (j : Fin Fs.length) :
    Fs.reverse.getD (Fs.length-1-j.val) (fun _ => 0) = Fs.getD j.val (fun _ => 0) := by
  have hrev : Fs.length-1-j.val < Fs.reverse.length := by simp only [List.length_reverse]; have := j.isLt; omega
  rw [List.getD_eq_getElem _ _ hrev,List.getElem_reverse,List.getD_eq_getElem _ _ j.isLt]
  congr 1
  have := j.isLt
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
