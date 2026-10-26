module

public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary

/-! Natural point tests for the original halo interior and boundary. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloInteriorAt (s t band a b k : ℕ) : Bool :=
  decide (a+band ≤ k ∧ k < b-band ∧ naturalPhase s t (k-band) = naturalPhase s t (k+band))

def haloMaskAt (boundary : Bool) (s t band a b k : ℕ) : Bool :=
  if boundary then decide (a ≤ k ∧ k < b) && !haloInteriorAt s t band a b k
  else haloInteriorAt s t band a b k

theorem haloInteriorAt_spec {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b k : ℕ) (hb : b ≤ s) (hk : k < s) :
    haloInteriorAt s t band a b k = true ↔ (k : ZMod s) ∈ haloInterior s t band a b := by
  have hs : 0 < s := NeZero.pos s
  have hval : (k : ZMod s).val = k := ZMod.val_cast_of_lt hk
  have hnat (n : ℕ) : (naturalPhase s t n : ℤ) = PhaseCell.phase s t n :=
    (phaseIndex_nat hst.le n).symm.trans (phaseIndex_eq hs n)
  simp only [haloInteriorAt,decide_eq_true_eq,haloInterior,Finset.mem_filter,
    mem_interiorSet,PhaseCellMatrix.Interior,hval]
  constructor
  · rintro ⟨ha,hkb,hphase⟩
    have hband : band ≤ k := by omega
    have hamb : k+band < s := by omega
    refine ⟨⟨hband,hamb,?_⟩,ha,hkb⟩
    have he : (naturalPhase s t (k-band) : ℤ) = (naturalPhase s t (k+band) : ℤ) := by exact_mod_cast hphase
    simpa only [hnat,Nat.cast_sub hband,Nat.cast_add] using he
  · rintro ⟨⟨hband,_,hphase⟩,ha,hkb⟩
    refine ⟨ha,hkb,?_⟩
    have he : PhaseCell.phase s t ((k-band : ℕ) : ℤ) = PhaseCell.phase s t ((k+band : ℕ) : ℤ) := by
      simpa only [Nat.cast_sub hband,Nat.cast_add] using hphase
    rw [← hnat,← hnat] at he
    exact_mod_cast he

theorem haloMaskAt_spec {s t : ℕ} [NeZero s] (boundary : Bool) (hst : s < t)
    (band a b k : ℕ) (hb : b ≤ s) (hk : k < s) :
    haloMaskAt boundary s t band a b k = true ↔
      (k : ZMod s) ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b) := by
  have hval : (k : ZMod s).val = k := ZMod.val_cast_of_lt hk
  cases boundary
  · exact haloInteriorAt_spec hst band a b k hb hk
  · simp [haloMaskAt,haloBoundary,Finset.mem_sdiff,mem_haloVertices,hval,
      ← haloInteriorAt_spec hst band a b k hb hk]

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
