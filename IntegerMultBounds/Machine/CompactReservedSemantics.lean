import IntegerMultBounds.Machine.CompactReservedOriginal

/-! Each physical reserved interval has exact signed Walsh semantics, including
continuations from already accrued precision under the shared signed guard. -/
namespace IntegerMultBounds.Machine.CompactReservedSemantics
noncomputable section
open CompactFallbackHeaders
open CompactFallbackAxisRun (Array Width)
open CompactFallbackSemantics (Grid decoded)
open Networks

def directions (inverse : Bool) (D K rho start n : ℕ) (hK : 0<K) (hr : rho<K) (hfit : start+n≤D) :=
  if inverse then CompactFallbackInverseSemantics.directions D K rho start n hK hr hfit
  else CompactFallbackSemantics.directions D K rho start n hK hr hfit

theorem directions_succ (inverse : Bool) (D K rho start n : ℕ) (hK : 0<K) (hr : rho<K) (hfit : start+(n+1)≤D) :
    directions inverse D K rho start (n+1) hK hr hfit=directions inverse D K rho start n hK hr (by omega)++
      [(if inverse then -1 else 1,ButterflyAxisWalsh.direction (bits D K) (selected K rho (start+n))
        (selected_lt D K rho (start+n) hK hr (by omega)))] := by
  cases inverse
  · exact CompactFallbackSemantics.directions_succ D K rho start n hK hr hfit
  · exact CompactFallbackInverseSemantics.directions_succ D K rho start n hK hr hfit

theorem step_grid (inverse : Bool) (D K rho ell q i j : ℕ) (hK : 0<K) (hr : rho<K)
    (hi : i<D) (hguard : j+1≤2*bits D K) (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f) :
    Grid D K ell q (j+1) (CompactReservedAxisRun.step inverse D K rho ell q i f) := by
  have ht := selected_lt D K rho i hK hr hi
  cases inverse
  · simp only [CompactReservedAxisRun.step,Bool.false_eq_true,ite_false,CompactFallbackSchedule.step,dite_eq_left ht]
    exact ButterflyIndependentGuardSemantics.forward_grid (bits D K) (selected K rho i) (polynomials ell) q j ht (by omega) f hw hg
  · simp only [CompactReservedAxisRun.step,ite_true,CompactFallbackInverseSchedule.step,dite_eq_left ht]
    exact ButterflyIndependentGuardSemantics.inverse_grid (bits D K) (selected K rho i) (polynomials ell) q j ht (by omega) f hw hg

theorem run_grid (inverse : Bool) (D K rho ell q start n j : ℕ) (hK : 0<K) (hr : rho<K)
    (hfit : start+n≤D) (hguard : j+n≤2*bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f) :
    Grid D K ell q (j+n) (CompactReservedAxisRun.run inverse D K rho ell q start n f) := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    rw [show j+(n+1)=j+n+1 by omega]
    exact step_grid inverse D K rho ell q (start+n) (j+n) hK hr (by omega) (by omega) _
      (CompactReservedAxisRun.width_run inverse D K rho ell q start n f hw) (ih (by omega) (by omega))

theorem step_decoded (inverse : Bool) (D K rho ell q i j : ℕ) (hK : 0<K) (hr : rho<K)
    (hi : i<D) (hguard : j+1≤2*bits D K) (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f)
    (x : BinaryWalsh.Address (bits D K)) (r : Fin (polynomials ell)) :
    decoded D K ell q (j+1) (CompactReservedAxisRun.step inverse D K rho ell q i f) (FlatCoordinateLayout.index x r)=
      BinaryWalsh.kernel (if inverse then -1 else 1)
        (ButterflyAxisWalsh.direction (bits D K) (selected K rho i) (selected_lt D K rho i hK hr hi))
        (fun y => decoded D K ell q j f (FlatCoordinateLayout.index y r)) x := by
  have ht := selected_lt D K rho i hK hr hi
  cases inverse
  · simp only [CompactReservedAxisRun.step,Bool.false_eq_true,ite_false,CompactFallbackSchedule.step,dite_eq_left ht]
    have he := ButterflyIndependentGuardSemantics.forward_decoded (bits D K) (selected K rho i) (polynomials ell) q j ht (by omega) f hw hg
    change decoded D K ell q (j+1) (CompactFallbackAxisRun.applyAxis D K rho ell q i ht f)=_ at he
    rw [congrFun he (FlatCoordinateLayout.index x r),ButterflyAxisWalsh.axis_walsh]
  · simp only [CompactReservedAxisRun.step,ite_true,CompactFallbackInverseSchedule.step,dite_eq_left ht]
    have he := ButterflyIndependentGuardSemantics.inverse_decoded (bits D K) (selected K rho i) (polynomials ell) q j ht (by omega) f hw hg
    change decoded D K ell q (j+1) (CompactFallbackInverseAxis.applyAxis D K rho ell q i ht f)=_ at he
    rw [congrFun he (FlatCoordinateLayout.index x r),ButterflyInverseAxisSemantics.axis_walsh]

theorem kernelRun_append {D : ℕ} (as bs : List (ZMod 4 × BinaryWalsh.Address D))
    (f : BinaryWalsh.Arrays D) : BinaryWalsh.kernelRun (as++bs) f=
      BinaryWalsh.kernelRun bs (BinaryWalsh.kernelRun as f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

theorem decoded_run (inverse : Bool) (D K rho ell q start n j : ℕ) (hK : 0<K) (hr : rho<K)
    (hfit : start+n≤D) (hguard : j+n≤2*bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f) (r : Fin (polynomials ell)) :
    (fun x => decoded D K ell q (j+n) (CompactReservedAxisRun.run inverse D K rho ell q start n f)
      (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (directions inverse D K rho start n hK hr hfit)
        (fun x => decoded D K ell q j f (FlatCoordinateLayout.index x r)) := by
  induction n with
  | zero => cases inverse <;> simp [CompactReservedAxisRun.run,directions,CompactFallbackInverseSemantics.directions,
      CompactFallbackSemantics.directions,BinaryWalsh.negateKernels,BinaryWalsh.kernelRun]
  | succ n ih =>
    funext x
    rw [show j+(n+1)=j+n+1 by omega]
    change decoded D K ell q (j+n+1) (CompactReservedAxisRun.step inverse D K rho ell q (start+n)
      (CompactReservedAxisRun.run inverse D K rho ell q start n f)) (FlatCoordinateLayout.index x r)=_
    rw [step_decoded inverse D K rho ell q (start+n) (j+n) hK hr (by omega) (by omega) _
      (CompactReservedAxisRun.width_run inverse D K rho ell q start n f hw)
      (run_grid inverse D K rho ell q start n j hK hr (by omega) (by omega) f hw hg),
      ih (by omega) (by omega),directions_succ,kernelRun_append]
    rfl

end
end IntegerMultBounds.Machine.CompactReservedSemantics
