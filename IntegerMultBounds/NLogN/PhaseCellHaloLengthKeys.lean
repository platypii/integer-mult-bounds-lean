module

public import IntegerMultBounds.NLogN.PhaseCellHaloGeometry

/-! Artificial endpoint clipping adds at most two length candidates to the
four ambient candidates. The generated schedule therefore has at most six keys. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

theorem haloPhase_left_cut {s t : ℕ} [NeZero s] (hst : s < t) (band a b phase : ℕ)
    (hpos : 0 < haloLength s t band a b phase) (hcut : naturalStart s t band phase < a+band) :
    phase = naturalPhase s t (a+band) := by
  have hlt : haloStart s t band a phase < haloStop s t band b phase := by
    change 0 < haloStop s t band b phase-haloStart s t band a phase at hpos
    omega
  have hstart : haloStart s t band a phase = a+band := max_eq_right hcut.le
  have hjs : a+band < s := by rw [hstart] at hlt; exact hlt.trans_le (haloStop_le s t band b phase)
  have hv : ((a+band : ℕ) : ZMod s).val = a+band := ZMod.val_cast_of_lt hjs
  have hm := (haloInterior_phase_iff hst band a b phase ((a+band : ℕ) : ZMod s)).mpr
    (by rw [hv]; rw [hstart] at hlt ⊢; exact ⟨le_rfl,hlt⟩)
  have he := (cell_eq_naturalPhase hst ((a+band : ℕ) : ZMod s)).symm.trans hm.2
  rw [hv] at he
  exact (Int.natCast_inj.mp he).symm

theorem haloPhase_right_cut {s t : ℕ} [NeZero s] (hst : s < t) (band a b phase : ℕ)
    (hpos : 0 < haloLength s t band a b phase) (hcut : b-band < naturalStop s t band phase) :
    phase = naturalPhase s t (b-band-1) := by
  have hlt : haloStart s t band a phase < haloStop s t band b phase := by
    change 0 < haloStop s t band b phase-haloStart s t band a phase at hpos
    omega
  have hstop : haloStop s t band b phase = b-band := min_eq_right hcut.le
  have hjs : b-band-1 < s := by have hh := haloStop_le s t band b phase; rw [hstop] at hlt hh; omega
  have hv : ((b-band-1 : ℕ) : ZMod s).val = b-band-1 := ZMod.val_cast_of_lt hjs
  have hm := (haloInterior_phase_iff hst band a b phase ((b-band-1 : ℕ) : ZMod s)).mpr (by
    rw [hv,hstop]
    rw [hstop] at hlt
    omega)
  have he := (cell_eq_naturalPhase hst ((b-band-1 : ℕ) : ZMod s)).symm.trans hm.2
  rw [hv] at he
  exact (Int.natCast_inj.mp he).symm

def haloLengthCandidates (s t band a b : ℕ) : List ℕ :=
  naturalLengthCandidates s t band++
    [haloLength s t band a b (naturalPhase s t (a+band)),
      haloLength s t band a b (naturalPhase s t (b-band-1))]

theorem haloLength_mem_candidates {s t : ℕ} [NeZero s] (hst : s < t) (band a b phase : ℕ)
    (hphase : phase ∈ haloCellPhases s t band a b) :
    haloLength s t band a b phase ∈ haloLengthCandidates s t band a b := by
  obtain ⟨hp,hpos⟩ := (mem_haloCellPhases s t band a b phase).mp hphase
  by_cases hleft : naturalStart s t band phase < a+band
  · have he := haloPhase_left_cut hst band a b phase hpos hleft
    simp [haloLengthCandidates,he]
  by_cases hright : b-band < naturalStop s t band phase
  · have he := haloPhase_right_cut hst band a b phase hpos hright
    simp [haloLengthCandidates,he]
  have hlen : haloLength s t band a b phase = naturalLength s t band phase := by
    simp only [haloLength,haloStart,haloStop,max_eq_left (by omega : a+band ≤ naturalStart s t band phase),
      min_eq_left (by omega : naturalStop s t band phase ≤ b-band),naturalLength]
  rw [hlen]
  exact List.mem_append_left _ (naturalLength_mem_candidates hst band hp)

theorem haloLengthCandidates_uniform {s t L : ℕ} (hst : s < t) (band a b : ℕ)
    (hL : L ∈ haloLengthCandidates s t band a b) : L ≤ (s/(t-s)+1)-2*band := by
  rcases List.mem_append.mp hL with h | h
  · exact naturalLengthCandidates_uniform hst band h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    all_goals exact (haloLength_le_naturalLength _ _ _ _ _ _).trans (naturalLength_le_uniform hst band _)

def haloLengthKeys (s t band a b : ℕ) : List ℕ :=
  (haloLengthCandidates s t band a b).dedup.filter (fun L => decide (0 < L))

theorem haloLengthKeys_nodup (s t band a b : ℕ) : (haloLengthKeys s t band a b).Nodup :=
  (List.nodup_dedup _).filter _

theorem haloLengthKeys_length_le (s t band a b : ℕ) : (haloLengthKeys s t band a b).length ≤ 6 := by
  have hsub : (haloLengthKeys s t band a b).Sublist (haloLengthCandidates s t band a b) :=
    List.filter_sublist.trans (List.dedup_sublist _)
  simpa only [haloLengthCandidates,naturalLengthCandidates,List.length_append,List.length_cons,List.length_nil] using hsub.length_le

theorem haloLengthKeys_cover {s t : ℕ} [NeZero s] (hst : s < t) (band a b phase : ℕ)
    (hphase : phase ∈ haloCellPhases s t band a b) :
    haloLength s t band a b phase ∈ haloLengthKeys s t band a b := by
  have hc := haloLength_mem_candidates hst band a b phase hphase
  have hp := ((mem_haloCellPhases s t band a b phase).mp hphase).2
  simpa only [haloLengthKeys,List.mem_filter,List.mem_dedup,decide_eq_true_eq] using And.intro hc hp

theorem haloLengthKeys_pad {s t : ℕ} (hst : s < t) (band a b l : ℕ)
    (hpad : 2*((s/(t-s)+1)-2*band) ≤ 2^l+1) :
    ∀ L ∈ haloLengthKeys s t band a b, L+L ≤ 2^l+1 := by
  intro L hL
  have hc : L ∈ haloLengthCandidates s t band a b := by
    simpa only [List.mem_dedup] using (List.mem_filter.mp hL).1
  have hh := haloLengthCandidates_uniform hst band a b hc
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
