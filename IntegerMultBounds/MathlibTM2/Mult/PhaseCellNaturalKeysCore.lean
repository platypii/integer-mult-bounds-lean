module

public import IntegerMultBounds.NLogN.PhaseCellNaturalLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead

/-! The bounded length-key schedule covers exactly the original ambient
interior cores. Publishing their uniform errors introduces no key-count factor. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalKeyCores (s t band : ℕ) [NeZero s] : Finset (ZMod s) :=
  (naturalLengthKeys s t band).toFinset.biUnion (fun L =>
    (Finset.range (naturalLengthGroup s t band L).length).biUnion (fun n =>
      publishedCellCore (naturalGroupOrigin s t band L n) L))

theorem naturalLengthKeys_core_cover {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ)
    (j : ZMod s) (hj : j ∈ interiorSet s t band) :
    ∃ L ∈ naturalLengthKeys s t band, ∃ n : Fin (naturalLengthGroup s t band L).length,
      j ∈ publishedCellCore (naturalGroupOrigin s t band L n) L := by
  obtain ⟨L, hL, phase, hp, hspan⟩ := naturalLengthKeys_cover hst band j ((mem_interiorSet band j).mp hj)
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp hp
  have hphase : naturalGroupPhase s t band L n = phase := by
    unfold naturalGroupPhase
    rw [List.getD_eq_getElem _ _ hn, hget]
  have horigin : (naturalGroupOrigin s t band L n).val = naturalStart s t band phase := by
    rw [naturalGroupOrigin_val band L ⟨n, hn⟩, hphase]
  have hlen := ((mem_naturalLengthGroup s t band L phase).mp hp).2.2
  let i := j.val-(naturalGroupOrigin s t band L n).val
  have hi : i < L := by
    dsimp only [i]
    unfold naturalLength at hlen
    omega
  have he : (naturalGroupOrigin s t band L n).val+i = j.val := by dsimp [i]; omega
  have hcast : naturalGroupOrigin s t band L n+(i : ZMod s) = j := by
    simpa only [Nat.cast_add, ZMod.natCast_zmod_val] using congrArg (fun a : ℕ => (a : ZMod s)) he
  exact ⟨L, hL, ⟨n, hn⟩, Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, hcast⟩⟩

theorem naturalKeyCores_eq_interior {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ) :
    naturalKeyCores s t band = interiorSet s t band := by
  ext j
  constructor
  · intro hj
    obtain ⟨L, _, hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨n, hn, hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact ((naturalGroup_solver_geometry hst band L ⟨n, Finset.mem_range.mp hn⟩).2.2.1 i (Finset.mem_range.mp hi)).2
  · intro hj
    obtain ⟨L, hL, n, hj⟩ := naturalLengthKeys_core_cover hst band j hj
    exact Finset.mem_biUnion.mpr ⟨L, List.mem_toFinset.mpr hL,
      Finset.mem_biUnion.mpr ⟨n.val, Finset.mem_range.mpr n.isLt, hj⟩⟩

/-- The same uniform error survives publication over the complete interior. -/
theorem naturalLengthKeys_errorOn {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ)
    (out target : ZMod s → ℝ) (error : ℝ)
    (hlocal : ∀ L ∈ naturalLengthKeys s t band, ∀ n : Fin (naturalLengthGroup s t band L).length,
      PhaseCellInterface.ErrorOn (publishedCellCore (naturalGroupOrigin s t band L n) L) out target error) :
    PhaseCellInterface.ErrorOn (interiorSet s t band) out target error := by
  intro j hj
  obtain ⟨L, hL, n, hcore⟩ := naturalLengthKeys_core_cover hst band j hj
  exact hlocal L hL n j hcore

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
