module

public import IntegerMultBounds.NLogN.PhaseCellNaturalLengths
public import IntegerMultBounds.NLogN.PhaseCellNaturalVolume

/-! At most four nonempty equal-length batches cover all original interior
cells. Keys are computed from fixed candidates and preserve exact volume. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open scoped BigOperators

def naturalLengthKeys (s t band : ℕ) : List ℕ :=
  (naturalLengthCandidates s t band).dedup.filter
    (fun L => decide (0 < (naturalLengthGroup s t band L).length))

theorem naturalLengthKeys_nodup (s t band : ℕ) : (naturalLengthKeys s t band).Nodup :=
  (List.nodup_dedup _).filter _

theorem naturalLengthKeys_sublist (s t band : ℕ) :
    (naturalLengthKeys s t band).Sublist (naturalLengthCandidates s t band) :=
  List.filter_sublist.trans (List.dedup_sublist _)

theorem naturalLengthKeys_length_le (s t band : ℕ) : (naturalLengthKeys s t band).length ≤ 4 := by
  simpa only [naturalLengthCandidates, List.length_cons, List.length_nil] using
    (naturalLengthKeys_sublist s t band).length_le

theorem mem_naturalLengthKeys {s t : ℕ} (hst : s < t) (band L : ℕ) :
    L ∈ naturalLengthKeys s t band ↔ 0 < (naturalLengthGroup s t band L).length := by
  constructor
  · intro hL
    simpa only [naturalLengthKeys, List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hL).2
  · intro hL
    have hp := naturalGroupPhase_mem s t band L ⟨0, hL⟩
    obtain ⟨hphase, _, he⟩ := (mem_naturalLengthGroup s t band L _).mp hp
    have hc := naturalLength_mem_candidates hst band hphase
    rw [he] at hc
    simpa [naturalLengthKeys, hc] using hL

theorem naturalLengthKey_pos {s t : ℕ} (hst : s < t) (band L : ℕ)
    (hL : L ∈ naturalLengthKeys s t band) : 0 < L := by
  have hB := (mem_naturalLengthKeys hst band L).mp hL
  exact ((mem_naturalLengthGroup s t band L _).mp (naturalGroupPhase_mem s t band L ⟨0, hB⟩)).2.1

theorem naturalLengthKey_uniform {s t : ℕ} (hst : s < t) (band L : ℕ)
    (hL : L ∈ naturalLengthKeys s t band) : L ≤ (s/(t-s)+1)-2*band := by
  have hB := (mem_naturalLengthKeys hst band L).mp hL
  have hp := naturalGroupPhase_mem s t band L ⟨0, hB⟩
  have he := ((mem_naturalLengthGroup s t band L _).mp hp).2.2
  rw [← he]
  exact naturalLength_le_uniform hst band _

/-- One common FFT padding choice supports every nonempty length class. -/
theorem naturalLengthKeys_pad {s t : ℕ} (hst : s < t) (band l : ℕ)
    (hpad : 2*((s/(t-s)+1)-2*band) ≤ 2^l+1) :
    ∀ L ∈ naturalLengthKeys s t band, L+L ≤ 2^l+1 := by
  intro L hL
  have hh := naturalLengthKey_uniform hst band L hL
  omega

theorem naturalLengthGroup_nodup (s t band L : ℕ) : (naturalLengthGroup s t band L).Nodup :=
  (List.nodup_range).filter _

theorem naturalLengthGroup_toFinset (s t band L : ℕ) :
    (naturalLengthGroup s t band L).toFinset =
      (Finset.range (t-s+1)).filter (fun phase => 0 < L ∧ naturalLength s t band phase = L) := by
  ext phase
  simp [naturalLengthGroup]

/-- The four-key schedule covers every original interior coordinate. -/
theorem naturalLengthKeys_cover {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ)
    (j : ZMod s) (hj : PhaseCellMatrix.Interior s t band j) :
    ∃ L ∈ naturalLengthKeys s t band, ∃ phase ∈ naturalLengthGroup s t band L,
      naturalStart s t band phase ≤ j.val ∧ j.val < naturalStop s t band phase := by
  obtain ⟨L, phase, hp, hspan⟩ := naturalGroups_cover hst band j hj
  exact ⟨L, (mem_naturalLengthKeys hst band L).mpr (List.length_pos_of_mem hp), phase, hp, hspan⟩

/-- Grouping all nonempty lengths preserves exactly the original interior volume. -/
theorem naturalLengthKeys_volume {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ) :
    ∑ L ∈ (naturalLengthKeys s t band).toFinset, (naturalLengthGroup s t band L).length*L =
      (interiorSet s t band).card := by
  let phases := (Finset.range (t-s+1)).filter (fun phase => 0 < naturalLength s t band phase)
  have hmaps : ∀ phase ∈ phases,
      naturalLength s t band phase ∈ (naturalLengthKeys s t band).toFinset := by
    intro phase hp
    obtain ⟨hr, hpos⟩ := Finset.mem_filter.mp hp
    apply List.mem_toFinset.mpr
    apply (mem_naturalLengthKeys hst band _).mpr
    exact List.length_pos_of_mem ((mem_naturalLengthGroup s t band _ phase).mpr
      ⟨by have hh := Finset.mem_range.mp hr; omega, hpos, rfl⟩)
  have hfiber (L : ℕ) (hL : L ∈ (naturalLengthKeys s t band).toFinset) :
      (phases.filter (fun phase => naturalLength s t band phase = L)).card =
        (naturalLengthGroup s t band L).length := by
    have hpos := naturalLengthKey_pos hst band L (List.mem_toFinset.mp hL)
    have he : phases.filter (fun phase => naturalLength s t band phase = L) =
        (naturalLengthGroup s t band L).toFinset := by
      ext phase
      simp [phases, naturalLengthGroup_toFinset, hpos]
      omega
    rw [he]
    exact List.toFinset_card_of_nodup (naturalLengthGroup_nodup s t band L)
  have hh := Finset.sum_fiberwise_of_maps_to' hmaps (fun L : ℕ => L)
  have hsum : ∑ L ∈ (naturalLengthKeys s t band).toFinset, (naturalLengthGroup s t band L).length*L =
      ∑ phase ∈ phases, naturalLength s t band phase := by
    calc
      _ = ∑ L ∈ (naturalLengthKeys s t band).toFinset,
          (phases.filter (fun phase => naturalLength s t band phase = L)).card*L := by
        apply Finset.sum_congr rfl
        intro L hL
        rw [hfiber L hL]
      _ = _ := by simpa only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id] using hh
  rw [hsum, ← naturalIntervals_volume hst band]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro phase hp hn
  simp only [Finset.mem_filter, not_and] at hn
  exact Nat.eq_zero_of_not_pos (hn hp)

theorem naturalLengthKeys_list_volume {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ) :
    ((naturalLengthKeys s t band).map (fun L => (naturalLengthGroup s t band L).length*L)).sum =
      (interiorSet s t band).card := by
  rw [← List.sum_toFinset _ (naturalLengthKeys_nodup s t band)]
  exact naturalLengthKeys_volume hst band

theorem naturalLengthKeys_volume_le {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ) :
    ((naturalLengthKeys s t band).map (fun L => (naturalLengthGroup s t band L).length*L)).sum ≤ s := by
  rw [naturalLengthKeys_list_volume hst band]
  have hh := naturalIntervals_volume_le hst band
  rwa [naturalIntervals_volume hst band] at hh

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
