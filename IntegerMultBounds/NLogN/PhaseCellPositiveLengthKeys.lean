module

public import IntegerMultBounds.NLogN.PhaseCellNaturalLengthKeys

/-! Runtime selection removes zero and duplicate candidate lengths. Positive
candidates with no rows are skipped by testing the generated batch count. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalPositiveLengthKeys (s t band : ℕ) : List ℕ :=
  (naturalLengthCandidates s t band).dedup.filter (fun L => decide (0 < L))

theorem mem_naturalPositiveLengthKeys (s t band L : ℕ) :
    L ∈ naturalPositiveLengthKeys s t band ↔ L ∈ naturalLengthCandidates s t band ∧ 0 < L := by
  simp [naturalPositiveLengthKeys]

theorem naturalPositiveLengthKey_le_ambient {s t : ℕ} (hst : s < t) (band L : ℕ)
    (hband : 0 < band) (hL : L ∈ naturalPositiveLengthKeys s t band) : L ≤ s := by
  have hh := naturalLengthCandidates_uniform hst band ((mem_naturalPositiveLengthKeys s t band L).mp hL).1
  have hdiv := Nat.div_le_self s (t-s)
  omega

theorem naturalPositiveLengthKeys_nodup (s t band : ℕ) : (naturalPositiveLengthKeys s t band).Nodup :=
  (List.nodup_dedup _).filter _

theorem naturalPositiveLengthKeys_length_le (s t band : ℕ) :
    (naturalPositiveLengthKeys s t band).length ≤ 4 := by
  have hh : (naturalPositiveLengthKeys s t band).Sublist (naturalLengthCandidates s t band) :=
    List.filter_sublist.trans (List.dedup_sublist _)
  simpa only [naturalLengthCandidates, List.length_cons, List.length_nil] using hh.length_le

theorem naturalLengthKeys_eq_positive_filter (s t band : ℕ) :
    naturalLengthKeys s t band = (naturalPositiveLengthKeys s t band).filter
      (fun L => decide (0 < (naturalLengthGroup s t band L).length)) := by
  unfold naturalLengthKeys naturalPositiveLengthKeys
  rw [List.filter_filter]
  apply List.filter_congr
  intro L _
  by_cases hB : 0 < (naturalLengthGroup s t band L).length
  · have hL : 0 < L := ((mem_naturalLengthGroup s t band L _).mp
      (naturalGroupPhase_mem s t band L ⟨0, hB⟩)).2.1
    simp [hB, hL]
  · simp [hB]

theorem naturalLengthKeys_mem_positive (s t band L : ℕ)
    (hL : L ∈ naturalLengthKeys s t band) : L ∈ naturalPositiveLengthKeys s t band := by
  rw [naturalLengthKeys_eq_positive_filter] at hL
  exact (List.mem_filter.mp hL).1

/-- Empty candidates contribute zero paid row volume; the schedule's volume is exact. -/
theorem naturalPositiveLengthKeys_volume {s t : ℕ} [NeZero s] (hst : s < t) (band : ℕ) :
    ((naturalPositiveLengthKeys s t band).map (fun L => (naturalLengthGroup s t band L).length*L)).sum =
      (interiorSet s t band).card := by
  have hdrop (xs : List ℕ) :
      ((xs.filter (fun L => decide (0 < (naturalLengthGroup s t band L).length))).map
        (fun L => (naturalLengthGroup s t band L).length*L)).sum =
      (xs.map (fun L => (naturalLengthGroup s t band L).length*L)).sum := by
    induction xs with
    | nil => rfl
    | cons L xs ih =>
      by_cases hB : 0 < (naturalLengthGroup s t band L).length
      · simp [hB, ih]
      · have hz : (naturalLengthGroup s t band L).length = 0 := by omega
        simp [hz, ih]
  rw [← hdrop, ← naturalLengthKeys_eq_positive_filter]
  exact naturalLengthKeys_list_volume hst band

theorem naturalPositiveLengthKeys_pad {s t : ℕ} (hst : s < t) (band l : ℕ)
    (hpad : 2*((s/(t-s)+1)-2*band) ≤ 2^l+1) :
    ∀ L ∈ naturalPositiveLengthKeys s t band, L+L ≤ 2^l+1 := by
  intro L hL
  have hh := naturalLengthCandidates_uniform hst band ((mem_naturalPositiveLengthKeys s t band L).mp hL).1
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
