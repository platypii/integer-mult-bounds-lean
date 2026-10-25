module

public import IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-! # Computed full interior intervals of ambient phase cells

Empty phases produce length zero. A nonempty phase produces its least physical
coordinate and the span through its greatest coordinate. Convexity proves that
the span contains exactly the phase's interior vertices, without a supplied mask.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open Finset PhaseCellMatrix

/-- The finite physical coordinates used to generate interval endpoints. -/
def coordinateSet (s t w : ℕ) (phase : ℤ) : Finset ℕ :=
  (interiorIndices s t w phase).toFinset

def intervalStart (s t w : ℕ) (phase : ℤ) : ℕ :=
  if h : (coordinateSet s t w phase).Nonempty then (coordinateSet s t w phase).min' h else 0

def intervalLength (s t w : ℕ) (phase : ℤ) : ℕ :=
  if h : (coordinateSet s t w phase).Nonempty then
    (coordinateSet s t w phase).max' h - (coordinateSet s t w phase).min' h + 1 else 0

theorem mem_coordinateSet {s t : ℕ} [NeZero s] (w : ℕ) (phase : ℤ) (j : ZMod s) :
    j.val ∈ coordinateSet s t w phase ↔ Interior s t w j ∧ cell s t j = phase := by
  simpa only [coordinateSet, List.mem_toFinset] using mem_interiorIndices w phase j

theorem coordinateSet_lt (s t w : ℕ) (phase : ℤ) {j : ℕ} (hj : j ∈ coordinateSet s t w phase) : j < s :=
  interiorIndices_lt s t w phase (List.mem_toFinset.mp hj)

/-- Generated endpoints satisfy the exact full-cell geometry needed by the
interior solver. This does not introduce artificial halo cuts. -/
theorem generatedInterval_spec {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) (phase : ℤ)
    (k : ZMod s) (hk : Interior s t w k ∧ cell s t k = phase) :
    let lo : ZMod s := (intervalStart s t w phase : ℕ)
    let L := intervalLength s t w phase
    0 < L ∧ lo.val + L ≤ s ∧ cell s t lo = phase ∧
      (∀ a < L, Interior s t w (lo + (a : ZMod s)) ∧ cell s t (lo + (a : ZMod s)) = cell s t lo) ∧
      ∀ j : ZMod s, (Interior s t w j ∧ cell s t j = phase) ↔ ∃ a < L, lo + (a : ZMod s) = j := by
  let N := coordinateSet s t w phase
  have hkN : k.val ∈ N := (mem_coordinateSet w phase k).mpr hk
  have hn : N.Nonempty := ⟨k.val, hkN⟩
  let a := N.min' hn
  let b := N.max' hn
  have haN : a ∈ N := min'_mem N hn
  have hbN : b ∈ N := max'_mem N hn
  have has : a < s := coordinateSet_lt s t w phase haN
  have hbs : b < s := coordinateSet_lt s t w phase hbN
  have hab : a ≤ b := min'_le N b hbN
  let lo : ZMod s := (a : ZMod s)
  let lastVertex : ZMod s := (b : ZMod s)
  have hlo : lo.val = a := ZMod.val_cast_of_lt has
  have hhi : lastVertex.val = b := ZMod.val_cast_of_lt hbs
  have hloSpec : Interior s t w lo ∧ cell s t lo = phase :=
    (mem_coordinateSet w phase lo).mp (by simpa only [hlo] using haN)
  have hhiSpec : Interior s t w lastVertex ∧ cell s t lastVertex = phase :=
    (mem_coordinateSet w phase lastVertex).mp (by simpa only [hhi] using hbN)
  have hstart : intervalStart s t w phase = a := by simp [intervalStart, N, hn, a]
  have hlength : intervalLength s t w phase = b - a + 1 := by simp [intervalLength, N, hn, a, b]
  have hval (i : ℕ) (hi : a + i ≤ b) : (lo + (i : ZMod s)).val = a + i := by
    have his : (i : ZMod s).val = i := ZMod.val_cast_of_lt (by omega)
    rw [ZMod.val_add_of_lt (by omega), hlo, his]
  have hcover (i : ℕ) (hi : i < b - a + 1) :
      Interior s t w (lo + (i : ZMod s)) ∧ cell s t (lo + (i : ZMod s)) = cell s t lo := by
    have hv := hval i (by omega)
    exact interior_convex s t hst w lo (lo + (i : ZMod s)) lastVertex hloSpec.1 hhiSpec.1
      (hloSpec.2.trans hhiSpec.2.symm) (by omega) (by omega)
  dsimp only
  rw [hstart, hlength]
  change 0 < b - a + 1 ∧ lo.val + (b - a + 1) ≤ s ∧ cell s t lo = phase ∧ _
  refine ⟨by omega, by omega, hloSpec.2, hcover, ?_⟩
  intro j
  constructor
  · intro hj
    have hjN := (mem_coordinateSet w phase j).mpr hj
    have haj : a ≤ j.val := min'_le N j.val hjN
    have hjb : j.val ≤ b := le_max' N j.val hjN
    refine ⟨j.val - a, by omega, ?_⟩
    apply ZMod.val_injective
    rw [hval _ (by omega)]
    omega
  · rintro ⟨i, hi, rfl⟩
    have h := hcover i hi
    exact ⟨h.1, h.2.trans hloSpec.2⟩

theorem intervalLength_pos_iff (s t w : ℕ) (phase : ℤ) :
    0 < intervalLength s t w phase ↔ (coordinateSet s t w phase).Nonempty := by
  unfold intervalLength
  split_ifs with h
  · simp only [h, iff_true]
    omega
  · simp [h]

/-- The computed mask and endpoints discharge the cell solver's geometry
premises without an arbitrary interval or interior-set input. -/
theorem generatedInterval_solver_geometry {s t : ℕ} [NeZero s] (hst : s < t) (w : ℕ) (phase : ℤ)
    (k : ZMod s) (hk : Interior s t w k ∧ cell s t k = phase) :
    let lo : ZMod s := (intervalStart s t w phase : ℕ)
    let L := intervalLength s t w phase
    let I := interiorSet s t w
    0 < L ∧ lo.val + L ≤ s ∧
      (∀ a < L, Interior s t w (lo + (a : ZMod s)) ∧ lo + (a : ZMod s) ∈ I) ∧
      (∀ a < L, cell s t (lo + (a : ZMod s)) = cell s t lo) ∧
      ∀ j ∈ I, cell s t j = cell s t lo → ∃ a < L, lo + (a : ZMod s) = j := by
  obtain ⟨hL, hfit, hphase, hcover, hmax⟩ := generatedInterval_spec hst w phase k hk
  refine ⟨hL, hfit, ?_, fun a ha => (hcover a ha).2, ?_⟩
  · intro a ha
    exact ⟨(hcover a ha).1, (mem_interiorSet w _).mpr (hcover a ha).1⟩
  · intro j hj hjc
    exact (hmax j).mp ⟨(mem_interiorSet w j).mp hj, hjc.trans hphase⟩

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
