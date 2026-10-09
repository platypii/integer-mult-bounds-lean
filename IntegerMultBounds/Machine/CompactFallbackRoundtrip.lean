import IntegerMultBounds.Machine.CompactFallbackInverseSemantics

/-! Paid sparse forward/inverse roundtrip with actual chunk geometry and
polynomial count unchanged. The independent reservation covers two sparse
passes; actual final precision is q+2D, not q+2(DK). -/
namespace IntegerMultBounds.Machine.CompactFallbackRoundtrip
noncomputable section
open CompactFallbackHeaders
open CompactFallbackAxisRun (Array Width volume)
open CompactFallbackSemantics (decoded Grid)
open CompactFallbackOriginal (bank)
open Networks

def forward (D K rho ell q : ℕ) (f : Array D K ell) :=
  CompactFallbackSchedule.run D K rho ell q 0 D f
def result (D K rho ell q : ℕ) (f : Array D K ell) :=
  CompactFallbackInverseSchedule.run D K rho ell q 0 D (forward D K rho ell q f)
def program := seq CompactFallbackOriginal.program CompactFallbackInverseOriginal.program
def constant := 2*CompactFallbackOriginal.constant+1

theorem width_result (D K rho ell q : ℕ) (f : Array D K ell) (hw : Width D K ell q f) :
    Width D K ell q (result D K rho ell q f) :=
  CompactFallbackInverseSchedule.width_run D K rho ell q 0 D _
    (CompactFallbackSchedule.width_run D K rho ell q 0 D f hw)

theorem runs (D K rho ell q : ℕ) (hD : 0<D) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime program (fun v => v=bank D K rho ell q f)
      (fun v => v=bank D K rho ell q (result D K rho ell q f)) (constant*volume D K ell q*D) := by
  have h0 := CompactFallbackOriginal.runs_linear D K rho ell q hD hK hr f hw
  have h1 := CompactFallbackInverseOriginal.runs_linear D K rho ell q hD hK hr
    (forward D K rho ell q f) (CompactFallbackSchedule.width_run D K rho ell q 0 D f hw)
  have hV := ButterflyAxisHeadersInstall.volume_pos (bits D K) (polynomials ell) (reservation D K q)
    (pow_pos (by decide) ell)
  have hp : 0<volume D K ell q*D := Nat.mul_pos hV hD
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by
    unfold constant CompactFallbackInverseOriginal.constant
    nlinarith)

theorem forward_grid (D K rho ell q : ℕ) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) (hu : ∀ i,‖decoded D K ell q 0 f i‖≤1) :
    Grid D K ell q D (forward D K rho ell q f) :=
  CompactFallbackSemantics.run_grid D K rho ell q 0 D hK hr (by omega) f hw
    (ButterflyIndependentGuardSemantics.initial_grid (bits D K) (polynomials ell) q f hu)

theorem result_grid (D K rho ell q : ℕ) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) (hu : ∀ i,‖decoded D K ell q 0 f i‖≤1) :
    Grid D K ell q (2*D) (result D K rho ell q f) := by
  have hDB : D≤bits D K := Nat.le_mul_of_pos_right D hK
  have hh := CompactFallbackInverseSemantics.run_grid_from D K rho ell q 0 D D hK hr (by omega) (by omega)
    (forward D K rho ell q f) (CompactFallbackSchedule.width_run D K rho ell q 0 D f hw)
    (forward_grid D K rho ell q hK hr f hw hu)
  simpa only [←two_mul,result] using hh

/-- Exact sparse roundtrip at actual precision q+2D, without an intermediate
normalization assumption or a change to the physical coefficient layout. -/
theorem decoded_result (D K rho ell q : ℕ) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) (hu : ∀ i,‖decoded D K ell q 0 f i‖≤1)
    (r : Fin (polynomials ell)) :
    (fun x => decoded D K ell q (2*D) (result D K rho ell q f) (FlatCoordinateLayout.index x r))=
      (fun x => decoded D K ell q 0 f (FlatCoordinateLayout.index x r)) := by
  have hDB : D≤bits D K := Nat.le_mul_of_pos_right D hK
  have hf := CompactFallbackSemantics.decoded_run D K rho ell q 0 D hK hr (by omega) f hw
    (ButterflyIndependentGuardSemantics.initial_grid (bits D K) (polynomials ell) q f hu) r
  change (fun x => decoded D K ell q D (forward D K rho ell q f) (FlatCoordinateLayout.index x r))=_ at hf
  have hi := CompactFallbackInverseSemantics.decoded_run_from D K rho ell q 0 D D hK hr (by omega) (by omega)
    (forward D K rho ell q f) (CompactFallbackSchedule.width_run D K rho ell q 0 D f hw)
    (forward_grid D K rho ell q hK hr f hw hu) r
  change (fun x => decoded D K ell q (D+D) (result D K rho ell q f) (FlatCoordinateLayout.index x r))=
    BinaryWalsh.kernelRun (BinaryWalsh.negateKernels (CompactFallbackSemantics.directions D K rho 0 D hK hr (by omega)))
      (fun x => decoded D K ell q D (forward D K rho ell q f) (FlatCoordinateLayout.index x r)) at hi
  rw [hf,ButterflyInverseAxisCorrect.kernelRun_inverse] at hi
  simpa only [←two_mul] using hi

theorem correct (D K rho ell q : ℕ) (hD : 0<D) (hK : 0<K) (hr : rho<K)
    (f : Array D K ell) (hw : Width D K ell q f) (hu : ∀ i,‖decoded D K ell q 0 f i‖≤1) :
    HoareTime program (fun v => v=bank D K rho ell q f)
      (fun v => v=bank D K rho ell q (result D K rho ell q f) ∧
        ∀ r : Fin (polynomials ell),
          (fun x => decoded D K ell q (2*D) (result D K rho ell q f) (FlatCoordinateLayout.index x r))=
            (fun x => decoded D K ell q 0 f (FlatCoordinateLayout.index x r)))
      (constant*volume D K ell q*D) :=
  (runs D K rho ell q hD hK hr f hw).consequence (fun _ h => h)
    (fun _ h => ⟨h,fun r => decoded_result D K rho ell q hK hr f hw hu r⟩) le_rfl

end
end IntegerMultBounds.Machine.CompactFallbackRoundtrip
