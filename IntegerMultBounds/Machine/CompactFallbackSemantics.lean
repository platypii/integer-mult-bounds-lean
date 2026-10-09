import IntegerMultBounds.Machine.CompactFallbackOriginal

/-! Exact binary-Walsh semantics of the actual sparse fallback. Each original
chunk contributes its single bit rho+i*K; all other address bits and trailing
polynomial coefficients remain spectators. The physically computed independent
reservation validates every actual prefix at precision q+j. -/
namespace IntegerMultBounds.Machine.CompactFallbackSemantics
noncomputable section
open CompactFallbackHeaders CompactFallbackAxisRun
open Networks

abbrev decoded (D K ell q j : ℕ) (f : Array D K ell) :=
  ButterflyIndependentGuardSemantics.decoded (bits D K) (polynomials ell) q j f
abbrev Grid (D K ell q j : ℕ) (f : Array D K ell) :=
  ButterflyIndependentGuardSemantics.Grid (bits D K) (polynomials ell) q j f

theorem run_grid (D K rho ell q start n : ℕ) (hK : 0<K) (hr : rho<K) (hfit : start+n≤D)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q 0 f) :
    Grid D K ell q n (CompactFallbackSchedule.run D K rho ell q start n f) := by
  have hDB : D≤bits D K := Nat.le_mul_of_pos_right D hK
  induction n with
  | zero => exact hg
  | succ n ih =>
    have ht := selected_lt D K rho (start+n) hK hr (by omega)
    simp only [CompactFallbackSchedule.run,CompactFallbackSchedule.step,dite_eq_left ht]
    exact ButterflyIndependentGuardSemantics.forward_grid (bits D K) (selected K rho (start+n))
      (polynomials ell) q n ht (by omega) _
      (CompactFallbackSchedule.width_run D K rho ell q start n f hw) (ih (by omega))

def directions (D K rho start n : ℕ) (hK : 0<K) (hr : rho<K) (hfit : start+n≤D) :
    List (ZMod 4 × BinaryWalsh.Address (bits D K)) :=
  List.ofFn (fun i : Fin n => (1,ButterflyAxisWalsh.direction (bits D K) (selected K rho (start+i))
    (selected_lt D K rho (start+i) hK hr (by have := i.isLt; omega))))

theorem directions_succ (D K rho start n : ℕ) (hK : 0<K) (hr : rho<K) (hfit : start+(n+1)≤D) :
    directions D K rho start (n+1) hK hr hfit=directions D K rho start n hK hr (by omega)++
      [(1,ButterflyAxisWalsh.direction (bits D K) (selected K rho (start+n))
        (selected_lt D K rho (start+n) hK hr (by omega)))] := by
  unfold directions
  rw [List.ofFn_succ',List.concat_eq_append]
  rfl

private theorem kernelRun_append {D : ℕ} (as bs : List (ZMod 4 × BinaryWalsh.Address D))
    (f : BinaryWalsh.Arrays D) : BinaryWalsh.kernelRun (as++bs) f=
      BinaryWalsh.kernelRun bs (BinaryWalsh.kernelRun as f) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

theorem decoded_run (D K rho ell q start n : ℕ) (hK : 0<K) (hr : rho<K) (hfit : start+n≤D)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q 0 f) (r : Fin (polynomials ell)) :
    (fun x => decoded D K ell q n (CompactFallbackSchedule.run D K rho ell q start n f) (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (directions D K rho start n hK hr hfit)
        (fun x => decoded D K ell q 0 f (FlatCoordinateLayout.index x r)) := by
  have hDB : D≤bits D K := Nat.le_mul_of_pos_right D hK
  induction n with
  | zero => simp [CompactFallbackSchedule.run,directions,BinaryWalsh.kernelRun]
  | succ n ih =>
    have ht := selected_lt D K rho (start+n) hK hr (by omega)
    have he := ButterflyIndependentGuardSemantics.forward_decoded (bits D K) (selected K rho (start+n))
      (polynomials ell) q n ht (by omega) _
      (CompactFallbackSchedule.width_run D K rho ell q start n f hw)
      (run_grid D K rho ell q start n hK hr (by omega) f hw hg)
    change decoded D K ell q (n+1) (applyAxis D K rho ell q (start+n) ht
      (CompactFallbackSchedule.run D K rho ell q start n f))=_ at he
    funext x
    simp only [CompactFallbackSchedule.run,CompactFallbackSchedule.step,dite_eq_left ht]
    rw [congrFun he (FlatCoordinateLayout.index x r),ButterflyAxisWalsh.axis_walsh,
      ih (by omega),directions_succ,kernelRun_append]
    rfl

/-- Full physical small fallback, exact sparse kernel list and certified native
volume cost, with only its five original headers retained at the end. -/
theorem correct (D K rho ell q : ℕ) (hD : 0<D) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) (hu : ∀ i,‖decoded D K ell q 0 f i‖≤1) :
    HoareTime CompactFallbackOriginal.program
      (fun v => v=CompactFallbackOriginal.bank D K rho ell q f)
      (fun v => v=CompactFallbackOriginal.bank D K rho ell q (CompactFallbackSchedule.run D K rho ell q 0 D f) ∧
        ∀ r : Fin (polynomials ell),
          (fun x => decoded D K ell q D (CompactFallbackSchedule.run D K rho ell q 0 D f) (FlatCoordinateLayout.index x r))=
            BinaryWalsh.kernelRun (directions D K rho 0 D hK hr (by omega))
              (fun x => decoded D K ell q 0 f (FlatCoordinateLayout.index x r)))
      (CompactFallbackOriginal.constant*volume D K ell q*D) := by
  have hg := ButterflyIndependentGuardSemantics.initial_grid (bits D K) (polynomials ell) q f hu
  exact (CompactFallbackOriginal.runs_linear D K rho ell q hD hK hr f hw).consequence (fun _ h => h)
    (fun _ h => ⟨h,fun r => decoded_run D K rho ell q 0 D hK hr (by omega) f hw hg r⟩) le_rfl

end
end IntegerMultBounds.Machine.CompactFallbackSemantics
