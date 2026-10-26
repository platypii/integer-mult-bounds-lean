module

public import IntegerMultBounds.NLogN.PhaseCellHaloGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead
import Mathlib.Data.List.GetD

/-! The generated halo keys cover exactly the clipped interior. A uniform
cell error remains uniform after publication across all length classes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloKeyCores (s t band a b : ℕ) [NeZero s] : Finset (ZMod s) :=
  (haloLengthKeys s t band a b).toFinset.biUnion (fun L =>
    (Finset.range (haloLengthGroup s t band a b L).length).biUnion (fun n =>
      publishedCellCore (haloGroupOrigin s t band a b L n) L))

theorem haloLengthKeys_core_cover {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ)
    (j : ZMod s) (hj : j ∈ haloInterior s t band a b) :
    ∃ L ∈ haloLengthKeys s t band a b, ∃ n : Fin (haloLengthGroup s t band a b L).length,
      j ∈ publishedCellCore (haloGroupOrigin s t band a b L n) L := by
  obtain ⟨L, hL, phase, hp, hspan⟩ := haloGroups_cover hst band a b j hj
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hp
  have hphase : haloGroupPhase s t band a b L n = phase := by
    unfold haloGroupPhase
    rw [List.getD_eq_getElem _ _ hn, hget]
  have horigin : (haloGroupOrigin s t band a b L n).val = haloStart s t band a phase := by
    rw [haloGroupOrigin_val band a b L ⟨n, hn⟩, hphase]
  have hlen := ((mem_haloLengthGroup s t band a b L phase).mp hp).2.2
  let i := j.val-(haloGroupOrigin s t band a b L n).val
  have hi : i < L := by
    dsimp only [i]
    unfold haloLength at hlen
    omega
  have he : (haloGroupOrigin s t band a b L n).val+i = j.val := by dsimp [i]; omega
  have hcast : haloGroupOrigin s t band a b L n+(i : ZMod s) = j := by
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using congrArg (fun a : ℕ => (a : ZMod s)) he
  exact ⟨L, hL, ⟨n, hn⟩, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hcast⟩⟩

theorem haloKeyCores_eq_interior {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) :
    haloKeyCores s t band a b = haloInterior s t band a b := by
  unfold haloKeyCores
  ext j
  simp only [Finset.mem_biUnion,List.mem_toFinset,Finset.mem_range]
  constructor
  · rintro ⟨L,_,n,hn,hj⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact ((haloGroup_solver_geometry hst band a b L ⟨n,hn⟩).2.2.1 i (Finset.mem_range.mp hi)).2
  · intro hj
    obtain ⟨L,hL,n,hcore⟩ := haloLengthKeys_core_cover hst band a b j hj
    exact ⟨L,hL,n.val,n.isLt,hcore⟩

/-- The same uniform error survives publication over the complete interior. -/
theorem haloLengthKeys_errorOn {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ)
    (out target : ZMod s → ℝ) (error : ℝ)
    (hlocal : ∀ L ∈ haloLengthKeys s t band a b, ∀ n : Fin (haloLengthGroup s t band a b L).length,
      PhaseCellInterface.ErrorOn (publishedCellCore (haloGroupOrigin s t band a b L n) L) out target error) :
    PhaseCellInterface.ErrorOn (haloInterior s t band a b) out target error := by
  intro j hj
  obtain ⟨L, hL, n, hcore⟩ := haloLengthKeys_core_cover hst band a b j hj
  exact hlocal L hL n j hcore

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
