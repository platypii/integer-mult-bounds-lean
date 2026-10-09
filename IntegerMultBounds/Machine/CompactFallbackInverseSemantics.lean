import IntegerMultBounds.Machine.CompactFallbackInverseOriginal
import IntegerMultBounds.Machine.CompactFallbackSemantics

/-! Sparse inverse semantics starting at an already accrued precision. The
forward phase's grid is consumed directly, with no fresh normalization premise. -/
namespace IntegerMultBounds.Machine.CompactFallbackInverseSemantics
noncomputable section
open CompactFallbackHeaders
open CompactFallbackAxisRun (Array Width)
open CompactFallbackSemantics (decoded Grid)
open Networks

theorem run_grid_from (D K rho ell q start n j : ℕ) (hK : 0<K) (hr : rho<K)
    (hfit : start+n≤D) (hguard : j+n≤2*bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f) :
    Grid D K ell q (j+n) (CompactFallbackInverseSchedule.run D K rho ell q start n f) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    have ht := selected_lt D K rho (start+n) hK hr (by omega)
    simp only [CompactFallbackInverseSchedule.run,CompactFallbackInverseSchedule.step,dite_eq_left ht]
    rw [show j+(n+1)=j+n+1 by omega]
    exact ButterflyIndependentGuardSemantics.inverse_grid (bits D K) (selected K rho (start+n))
        (polynomials ell) q (j+n) ht (by omega) _
        (CompactFallbackInverseSchedule.width_run D K rho ell q start n f hw)
        (ih (by omega) (by omega))

def directions (D K rho start n : ℕ) (hK : 0<K) (hr : rho<K) (hfit : start+n≤D) :=
  BinaryWalsh.negateKernels (CompactFallbackSemantics.directions D K rho start n hK hr hfit)

theorem directions_succ (D K rho start n : ℕ) (hK : 0<K) (hr : rho<K) (hfit : start+(n+1)≤D) :
    directions D K rho start (n+1) hK hr hfit=directions D K rho start n hK hr (by omega)++
      [(-1,ButterflyAxisWalsh.direction (bits D K) (selected K rho (start+n))
        (selected_lt D K rho (start+n) hK hr (by omega)))] := by
  simp only [directions,CompactFallbackSemantics.directions_succ,BinaryWalsh.negateKernels,
    List.map_append,List.map_cons,List.map_nil]

private theorem kernelRun_append {D : ℕ} (as bs : List (ZMod 4 × BinaryWalsh.Address D))
    (f : BinaryWalsh.Arrays D) : BinaryWalsh.kernelRun (as++bs) f=
      BinaryWalsh.kernelRun bs (BinaryWalsh.kernelRun as f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

theorem decoded_run_from (D K rho ell q start n j : ℕ) (hK : 0<K) (hr : rho<K)
    (hfit : start+n≤D) (hguard : j+n≤2*bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f) (r : Fin (polynomials ell)) :
    (fun x => decoded D K ell q (j+n) (CompactFallbackInverseSchedule.run D K rho ell q start n f)
      (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (directions D K rho start n hK hr hfit)
        (fun x => decoded D K ell q j f (FlatCoordinateLayout.index x r)) := by
  induction n with
  | zero => simp [CompactFallbackInverseSchedule.run,directions,CompactFallbackSemantics.directions,
      BinaryWalsh.negateKernels,BinaryWalsh.kernelRun]
  | succ n ih =>
    have ht := selected_lt D K rho (start+n) hK hr (by omega)
    have he := ButterflyIndependentGuardSemantics.inverse_decoded (bits D K) (selected K rho (start+n))
      (polynomials ell) q (j+n) ht (by omega) _
      (CompactFallbackInverseSchedule.width_run D K rho ell q start n f hw)
      (run_grid_from D K rho ell q start n j hK hr (by omega) (by omega) f hw hg)
    change decoded D K ell q (j+n+1) (CompactFallbackInverseAxis.applyAxis D K rho ell q (start+n) ht
      (CompactFallbackInverseSchedule.run D K rho ell q start n f))=_ at he
    funext x
    simp only [CompactFallbackInverseSchedule.run,CompactFallbackInverseSchedule.step,dite_eq_left ht]
    rw [show j+(n+1)=j+n+1 by omega,congrFun he (FlatCoordinateLayout.index x r),
      ButterflyInverseAxisSemantics.axis_walsh,ih (by omega) (by omega),directions_succ,kernelRun_append]
    rfl

end
end IntegerMultBounds.Machine.CompactFallbackInverseSemantics
