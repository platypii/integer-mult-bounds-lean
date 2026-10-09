import IntegerMultBounds.Machine.CompactReservedSemantics

/-! The full physically controlled low/high reservation schedule implements
exactly its two sparse signed-kernel lists, at the actual accrued precision. -/
namespace IntegerMultBounds.Machine.CompactReservedCorrect
noncomputable section
open CompactReservedHeaders
open CompactFallbackHeaders (bits polynomials)
open CompactFallbackAxisRun (Array Width word)
open CompactFallbackSemantics (Grid decoded)
open CompactReservedOriginal (result)
open CompactGadgetReservationCapacity (backChunks)
open Networks

def directions (inverse : Bool) (c m D K rho d G : ℕ) (hK : 0<K) (hr : rho<K)
    (hD : reserved c m d G K≤D) :=
  CompactReservedSemantics.directions inverse D K rho 0 (backChunks d G K) hK hr (by unfold reserved at hD; omega)++
  CompactReservedSemantics.directions inverse D K rho (D-high c m d G K) (high c m d G K) hK hr (by unfold reserved at hD; omega)

theorem directions_inverse (c m D K rho d G : ℕ) (hK : 0<K) (hr : rho<K)
    (hD : reserved c m d G K≤D) :
    directions true c m D K rho d G hK hr hD=
      BinaryWalsh.negateKernels (directions false c m D K rho d G hK hr hD) := by
  simp only [directions,CompactReservedSemantics.directions,Bool.false_eq_true,ite_false,ite_true,
    CompactFallbackInverseSemantics.directions,BinaryWalsh.negateKernels,List.map_append]

theorem result_grid (inverse : Bool) (c m D K rho ell q d G j : ℕ) (hK : 0<K) (hr : rho<K)
    (hD : reserved c m d G K≤D) (hguard : j+reserved c m d G K≤2*bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f) :
    Grid D K ell q (j+reserved c m d G K) (result inverse c m D K rho ell q d G f) := by
  have hb : backChunks d G K≤D := by unfold reserved at hD; omega
  have hh : high c m d G K≤D := by unfold reserved at hD; omega
  have hg0 := CompactReservedSemantics.run_grid inverse D K rho ell q 0 (backChunks d G K) j hK hr
    (by omega) (by unfold reserved at hguard; omega) f hw hg
  have hg1 := CompactReservedSemantics.run_grid inverse D K rho ell q (D-high c m d G K) (high c m d G K)
    (j+backChunks d G K) hK hr (by omega) (by unfold reserved at hguard; omega)
    (CompactReservedOriginal.low inverse D K rho ell q d G f)
    (CompactReservedAxisRun.width_run inverse D K rho ell q 0 (backChunks d G K) f hw) hg0
  rw [show j+reserved c m d G K=j+backChunks d G K+high c m d G K by unfold reserved; omega]
  exact hg1

theorem decoded_result (inverse : Bool) (c m D K rho ell q d G j : ℕ) (hK : 0<K) (hr : rho<K)
    (hD : reserved c m d G K≤D) (hguard : j+reserved c m d G K≤2*bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f) (r : Fin (polynomials ell)) :
    (fun x => decoded D K ell q (j+reserved c m d G K) (result inverse c m D K rho ell q d G f)
      (FlatCoordinateLayout.index x r))=
      BinaryWalsh.kernelRun (directions inverse c m D K rho d G hK hr hD)
        (fun x => decoded D K ell q j f (FlatCoordinateLayout.index x r)) := by
  have hb : backChunks d G K≤D := by unfold reserved at hD; omega
  have hh : high c m d G K≤D := by unfold reserved at hD; omega
  have hg0 := CompactReservedSemantics.run_grid inverse D K rho ell q 0 (backChunks d G K) j hK hr
    (by omega) (by unfold reserved at hguard; omega) f hw hg
  have he0 := CompactReservedSemantics.decoded_run inverse D K rho ell q 0 (backChunks d G K) j hK hr
    (by omega) (by unfold reserved at hguard; omega) f hw hg r
  have he1 := CompactReservedSemantics.decoded_run inverse D K rho ell q (D-high c m d G K) (high c m d G K)
    (j+backChunks d G K) hK hr (by omega) (by unfold reserved at hguard; omega)
    (CompactReservedOriginal.low inverse D K rho ell q d G f)
    (CompactReservedAxisRun.width_run inverse D K rho ell q 0 (backChunks d G K) f hw) hg0 r
  change (fun x => decoded D K ell q (j+backChunks d G K) (CompactReservedOriginal.low inverse D K rho ell q d G f)
    (FlatCoordinateLayout.index x r))=_ at he0
  rw [he0] at he1
  rw [directions,CompactReservedSemantics.kernelRun_append]
  rw [show j+reserved c m d G K=j+backChunks d G K+high c m d G K by unfold reserved; omega]
  exact he1

theorem correct (inverse : Bool) (c m D K rho ell q d G j : ℕ) (hc : 2≤c) (hm : 2≤m)
    (hd : 0<d) (hK : 0<K) (hr : rho<K) (hD : reserved c m d G K≤D)
    (hguard : j+reserved c m d G K≤2*bits D K)
    (f : Array D K ell) (hw : Width D K ell q f) (hg : Grid D K ell q j f) :
    HoareTime (CompactReservedOriginal.program inverse c m)
      (fun v => v=CompactReservedSchedule.bank (initial D K rho ell q d G) (word f))
      (fun v => v=CompactReservedSchedule.bank (initial D K rho ell q d G)
          (word (result inverse c m D K rho ell q d G f)) ∧
        ∀ r : Fin (polynomials ell),
          (fun x => decoded D K ell q (j+reserved c m d G K) (result inverse c m D K rho ell q d G f)
            (FlatCoordinateLayout.index x r))=
            BinaryWalsh.kernelRun (directions inverse c m D K rho d G hK hr hD)
              (fun x => decoded D K ell q j f (FlatCoordinateLayout.index x r)))
      (CompactReservedOriginal.cost c m D K rho ell q d G) :=
  (CompactReservedOriginal.runs inverse c m D K rho ell q d G hc hm hd hK hr hD f hw).consequence
    (fun _ h => h) (fun _ h => ⟨h,fun r => decoded_result inverse c m D K rho ell q d G j hK hr hD hguard f hw hg r⟩) le_rfl

end
end IntegerMultBounds.Machine.CompactReservedCorrect
