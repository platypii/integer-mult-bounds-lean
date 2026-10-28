module

public import IntegerMultBounds.NLogN.IntervalRunMask
public import IntegerMultBounds.NLogN.PhaseCellHaloGeometry
public import IntegerMultBounds.NLogN.PhaseCellHaloMask

/-! The actual halo interior is the rasterization of its ordered positive intervals. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloRunIntervals (s t band a b : ℕ) : List (ℕ × ℕ) :=
  (haloCellPhases s t band a b).map (fun phase =>
    (haloStart s t band a phase,haloStop s t band b phase))

theorem haloRunIntervals_ordered (s t band a b : ℕ) :
    IntervalRunMask.Ordered 0 s (haloRunIntervals s t band a b) := by
  apply IntervalRunMask.ordered_of_pairwise (Nat.zero_le s)
  · intro r hr; exact Nat.zero_le _
  · intro r hr
    obtain ⟨phase,hphase,rfl⟩ := List.mem_map.mp hr
    have hpos := (mem_haloCellPhases s t band a b phase).mp hphase
    have hs := haloStop_le s t band b phase
    dsimp only [haloLength] at hpos
    exact ⟨by omega,hs⟩
  · unfold haloRunIntervals
    rw [List.pairwise_map]
    have hp : (haloCellPhases s t band a b).Pairwise (· < ·) :=
      (List.pairwise_lt_range (n := t-s+1)).filter _
    exact hp.imp (fun {_ _} hlt => haloCells_ordered s t band a b _ _ hlt)

theorem haloRunIntervals_contains {s t : ℕ} [NeZero s] (hst : s < t) (band a b k : ℕ)
    (hb : b ≤ s) (hk : k < s) :
    IntervalRunMask.contains (haloRunIntervals s t band a b) k = true ↔
      haloInteriorAt s t band a b k = true := by
  have hv : (k : ZMod s).val = k := ZMod.val_cast_of_lt hk
  rw [IntervalRunMask.contains,List.any_eq_true]
  constructor
  · rintro ⟨r,hr,hflag⟩
    obtain ⟨phase,hphase,rfl⟩ := List.mem_map.mp hr
    have hpoint := of_decide_eq_true hflag
    apply (haloInteriorAt_spec hst band a b k hb hk).mpr
    exact ((haloInterior_phase_iff hst band a b phase (k : ZMod s)).mpr (by simpa only [hv] using hpoint)).1
  · intro hi
    have hI := (haloInteriorAt_spec hst band a b k hb hk).mp hi
    obtain ⟨phase,hphase,hpoint⟩ := haloCells_cover hst band a b (k : ZMod s) hI
    refine ⟨(haloStart s t band a phase,haloStop s t band b phase),List.mem_map.mpr ⟨phase,hphase,rfl⟩,?_⟩
    exact decide_eq_true (by simpa only [hv] using hpoint)

theorem haloRunMask_eq {s t : ℕ} [NeZero s] (hst : s < t) (band a b : ℕ) (hb : b ≤ s) :
    IntervalRunMask.mask 0 s (haloRunIntervals s t band a b) =
      (List.range s).map (haloInteriorAt s t band a b) := by
  rw [IntervalRunMask.mask_eq_map (haloRunIntervals_ordered s t band a b)]
  simp only [Nat.sub_zero,Nat.zero_add]
  apply List.map_congr_left
  intro k hk
  exact Bool.eq_iff_iff.mpr (haloRunIntervals_contains hst band a b k hb (List.mem_range.mp hk))

theorem haloRunIntervals_length_le (s t band a b : ℕ) :
    (haloRunIntervals s t band a b).length ≤ t-s+1 := by
  simp only [haloRunIntervals,List.length_map,haloCellPhases]
  simpa only [List.length_range] using List.length_filter_le
    (fun phase => decide (0 < haloLength s t band a b phase)) (List.range (t-s+1))

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
