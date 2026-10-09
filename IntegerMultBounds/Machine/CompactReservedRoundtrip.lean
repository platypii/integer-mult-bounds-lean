import IntegerMultBounds.Machine.CompactReservedCorrect

/-! Actual nonfallback forward/inverse reservation roundtrip. The inverse
consumes the forward grid and retained native word; all runtime ordinal and
count synthesis is included twice in the physical execution bound. -/
namespace IntegerMultBounds.Machine.CompactReservedRoundtrip
noncomputable section
open CompactReservedHeaders
open CompactFallbackHeaders (bits polynomials)
open CompactFallbackAxisRun (Array Width word)
open CompactFallbackSemantics (Grid decoded)
open Networks

def forward (c m D K rho ell q d G : ℕ) (f : Array D K ell) :=
  CompactReservedOriginal.result false c m D K rho ell q d G f
def result (c m D K rho ell q d G : ℕ) (f : Array D K ell) :=
  CompactReservedOriginal.result true c m D K rho ell q d G (forward c m D K rho ell q d G f)
def program (c m : ℕ) := seq (CompactReservedOriginal.program false c m) (CompactReservedOriginal.program true c m)
def cost (c m D K rho ell q d G : ℕ) := 2*CompactReservedOriginal.cost c m D K rho ell q d G+1

theorem forward_grid (c m D K rho ell q d G : ℕ) (hK : 0<K) (hr : rho<K)
    (hD : reserved c m d G K≤D) (f : Array D K ell) (hw : Width D K ell q f)
    (hu : ∀ i,‖decoded D K ell q 0 f i‖≤1) :
    Grid D K ell q (reserved c m d G K) (forward c m D K rho ell q d G f) := by
  have hDB : D≤bits D K := Nat.le_mul_of_pos_right D hK
  have hg := CompactReservedCorrect.result_grid false c m D K rho ell q d G 0 hK hr hD (by omega) f hw
    (ButterflyIndependentGuardSemantics.initial_grid (bits D K) (polynomials ell) q f hu)
  simpa only [Nat.zero_add,forward] using hg

theorem decoded_result (c m D K rho ell q d G : ℕ) (hK : 0<K) (hr : rho<K)
    (hD : reserved c m d G K≤D) (f : Array D K ell) (hw : Width D K ell q f)
    (hu : ∀ i,‖decoded D K ell q 0 f i‖≤1) (r : Fin (polynomials ell)) :
    (fun x => decoded D K ell q (2*reserved c m d G K) (result c m D K rho ell q d G f)
      (FlatCoordinateLayout.index x r))=(fun x => decoded D K ell q 0 f (FlatCoordinateLayout.index x r)) := by
  have hDB : D≤bits D K := Nat.le_mul_of_pos_right D hK
  have hf := CompactReservedCorrect.decoded_result false c m D K rho ell q d G 0 hK hr hD (by omega) f hw
    (ButterflyIndependentGuardSemantics.initial_grid (bits D K) (polynomials ell) q f hu) r
  simp only [Nat.zero_add] at hf
  change (fun x => decoded D K ell q (reserved c m d G K) (forward c m D K rho ell q d G f)
    (FlatCoordinateLayout.index x r))=_ at hf
  have hi := CompactReservedCorrect.decoded_result true c m D K rho ell q d G (reserved c m d G K)
    hK hr hD (by omega) (forward c m D K rho ell q d G f)
    (CompactReservedOriginal.width_result false c m D K rho ell q d G f hw)
    (forward_grid c m D K rho ell q d G hK hr hD f hw hu) r
  rw [hf,CompactReservedCorrect.directions_inverse,ButterflyInverseAxisCorrect.kernelRun_inverse] at hi
  simpa only [result,←two_mul] using hi

theorem runs (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hK : 0<K)
    (hr : rho<K) (hD : reserved c m d G K≤D) (f : Array D K ell) (hw : Width D K ell q f) :
    HoareTime (program c m)
      (fun v => v=CompactReservedSchedule.bank (initial D K rho ell q d G) (word f))
      (fun v => v=CompactReservedSchedule.bank (initial D K rho ell q d G) (word (result c m D K rho ell q d G f)))
      (cost c m D K rho ell q d G) := by
  have h0 := CompactReservedOriginal.runs false c m D K rho ell q d G hc hm hd hK hr hD f hw
  have h1 := CompactReservedOriginal.runs true c m D K rho ell q d G hc hm hd hK hr hD
    (forward c m D K rho ell q d G f) (CompactReservedOriginal.width_result false c m D K rho ell q d G f hw)
  exact (h0.seq h1).consequence (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem correct (c m D K rho ell q d G : ℕ) (hc : 2≤c) (hm : 2≤m) (hd : 0<d) (hK : 0<K)
    (hr : rho<K) (hD : reserved c m d G K≤D) (f : Array D K ell) (hw : Width D K ell q f)
    (hu : ∀ i,‖decoded D K ell q 0 f i‖≤1) :
    HoareTime (program c m)
      (fun v => v=CompactReservedSchedule.bank (initial D K rho ell q d G) (word f))
      (fun v => v=CompactReservedSchedule.bank (initial D K rho ell q d G) (word (result c m D K rho ell q d G f)) ∧
        ∀ r : Fin (polynomials ell),
          (fun x => decoded D K ell q (2*reserved c m d G K) (result c m D K rho ell q d G f)
            (FlatCoordinateLayout.index x r))=(fun x => decoded D K ell q 0 f (FlatCoordinateLayout.index x r)))
      (cost c m D K rho ell q d G) :=
  (runs c m D K rho ell q d G hc hm hd hK hr hD f hw).consequence (fun _ h => h)
    (fun _ h => ⟨h,fun r => decoded_result c m D K rho ell q d G hK hr hD f hw hu r⟩) le_rfl

end
end IntegerMultBounds.Machine.CompactReservedRoundtrip
