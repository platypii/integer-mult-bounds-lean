module

public import IntegerMultBounds.NLogN.PhaseCellNaturalInterval

/-! Identify natural division endpoints with the existing computed full-cell
intervals, including empty and clipped end cells. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem naturalStop_le (s t w phase : ℕ) : naturalStop s t w phase ≤ s :=
  (Nat.sub_le _ _).trans (min_le_left _ _)

theorem naturalLength_pos_iff (s t w phase : ℕ) :
    0 < naturalLength s t w phase ↔ naturalStart s t w phase < naturalStop s t w phase := by
  simp [naturalLength]

theorem naturalInterval_nonempty {s t : ℕ} (hs : 0 < s) (hst : s < t) (w phase : ℕ) :
    (coordinateSet s t w (phase : ℤ)).Nonempty ↔ 0 < naturalLength s t w phase := by
  rw [coordinateSet_eq_Ico hs hst, Finset.nonempty_Ico, naturalLength_pos_iff]

theorem intervalStart_eq_naturalStart {s t : ℕ} (hs : 0 < s) (hst : s < t) (w phase : ℕ)
    (hlen : 0 < naturalLength s t w phase) :
    intervalStart s t w (phase : ℤ) = naturalStart s t w phase := by
  have hn := (naturalInterval_nonempty hs hst w phase).mpr hlen
  rw [intervalStart, dite_eq_left hn]
  apply (Finset.min'_eq_iff _ hn _).mpr
  constructor
  · rw [coordinateSet_eq_Ico hs hst]
    exact Finset.mem_Ico.mpr ⟨le_rfl, (naturalLength_pos_iff s t w phase).mp hlen⟩
  · intro j hj
    rw [coordinateSet_eq_Ico hs hst] at hj
    exact (Finset.mem_Ico.mp hj).1

theorem intervalLength_eq_naturalLength {s t : ℕ} (hs : 0 < s) (hst : s < t) (w phase : ℕ) :
    intervalLength s t w (phase : ℤ) = naturalLength s t w phase := by
  by_cases hn : (coordinateSet s t w (phase : ℤ)).Nonempty
  · have hlen := (naturalInterval_nonempty hs hst w phase).mp hn
    have hlt := (naturalLength_pos_iff s t w phase).mp hlen
    have hmin : (coordinateSet s t w (phase : ℤ)).min' hn = naturalStart s t w phase := by
      simpa only [intervalStart, dite_eq_left hn] using intervalStart_eq_naturalStart hs hst w phase hlen
    have hmax : (coordinateSet s t w (phase : ℤ)).max' hn = naturalStop s t w phase-1 := by
      apply (Finset.max'_eq_iff _ hn _).mpr
      constructor
      · rw [coordinateSet_eq_Ico hs hst]
        apply Finset.mem_Ico.mpr
        omega
      · intro j hj
        rw [coordinateSet_eq_Ico hs hst] at hj
        have hh := (Finset.mem_Ico.mp hj).2
        omega
    simp only [intervalLength, dite_eq_left hn, hmax, hmin, naturalLength]
    omega
  · have hz : naturalLength s t w phase = 0 := by
      have hh := (naturalInterval_nonempty hs hst w phase).not.mp hn
      omega
    simp only [intervalLength, dite_eq_right hn, hz]

theorem naturalStart_lt {s t : ℕ} (w phase : ℕ) (hlen : 0 < naturalLength s t w phase) :
    naturalStart s t w phase < s :=
  ((naturalLength_pos_iff s t w phase).mp hlen).trans_le (naturalStop_le s t w phase)

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
