module

public import IntegerMultBounds.NLogN.PhaseCellHaloInterval
public import IntegerMultBounds.NLogN.PhaseCellNaturalLengths
public import IntegerMultBounds.NLogN.PhaseCellNaturalClassSeparation

/-! Positive clipped intervals discharge the existing cell solver's complete
geometry contract for the selected halo interior of the same ambient matrix. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

theorem haloLength_le_naturalLength (s t band a b phase : ℕ) :
    haloLength s t band a b phase ≤ naturalLength s t band phase := by
  dsimp only [haloLength,haloStop,haloStart,naturalLength]
  omega

theorem haloCells_ordered (s t band a b p q : ℕ) (hpq : p < q) :
    haloStop s t band b p ≤ haloStart s t band a q :=
  (min_le_left _ _).trans ((naturalStop_le_start hpq).trans (le_max_left _ _))

theorem haloCellPhases_nodup (s t band a b : ℕ) : (haloCellPhases s t band a b).Nodup :=
  (List.nodup_range (n := t-s+1)).filter _

theorem halo_solver_geometry {s t : ℕ} [NeZero s] (hst : s < t) (band a b phase : ℕ)
    (hpos : 0 < haloLength s t band a b phase) :
    let lo : ZMod s := (haloStart s t band a phase : ℕ)
    let L := haloLength s t band a b phase
    let I := haloInterior s t band a b
    0 < L ∧ lo.val+L ≤ s ∧
      (∀ i < L, Interior s t band (lo+(i : ZMod s)) ∧ lo+(i : ZMod s) ∈ I) ∧
      (∀ i < L, cell s t (lo+(i : ZMod s)) = cell s t lo) ∧
      ∀ j ∈ I, cell s t j = cell s t lo → ∃ i < L, lo+(i : ZMod s) = j := by
  dsimp only
  let start := haloStart s t band a phase
  let stop := haloStop s t band b phase
  let L := stop-start
  let lo : ZMod s := (start : ℕ)
  have hlt : start < stop := by change 0 < stop-start at hpos; omega
  have hstop : stop ≤ s := haloStop_le s t band b phase
  have hlo : lo.val = start := ZMod.val_cast_of_lt (by omega)
  have hpoint (i : ℕ) (hi : i < L) :
      (lo+(i : ZMod s)).val = start+i ∧
      lo+(i : ZMod s) ∈ haloInterior s t band a b ∧ cell s t (lo+(i : ZMod s)) = (phase : ℤ) := by
    have hi' : start+i < stop := by dsimp only [L] at hi; omega
    have hv : (lo+(i : ZMod s)).val = start+i := by
      simpa only [Nat.cast_add] using (ZMod.val_cast_of_lt (show start+i < s by omega) :
        ((start+i : ℕ) : ZMod s).val = start+i)
    refine ⟨hv,(haloInterior_phase_iff hst band a b phase _).mpr ?_⟩
    rw [hv]
    exact ⟨by omega,hi'⟩
  have hzero := (hpoint 0 (by dsimp only [L]; omega)).2
  have horigin : cell s t lo = (phase : ℤ) := by simpa using hzero.2
  refine ⟨hpos,?_,?_,?_,?_⟩
  · change lo.val+L ≤ s
    rw [hlo]
    dsimp only [L]
    omega
  · intro i hi
    have hm := (hpoint i hi).2.1
    exact ⟨(mem_interiorSet band _).mp (Finset.mem_filter.mp hm).1,hm⟩
  · intro i hi
    exact (hpoint i hi).2.2.trans horigin.symm
  · intro j hj hjc
    obtain ⟨ha,hb⟩ := (haloInterior_phase_iff hst band a b phase j).mp ⟨hj,hjc.trans horigin⟩
    have hi : j.val-start < L := by dsimp only [L]; omega
    refine ⟨j.val-start,hi,?_⟩
    apply ZMod.val_injective
    rw [(hpoint (j.val-start) hi).1]
    omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
