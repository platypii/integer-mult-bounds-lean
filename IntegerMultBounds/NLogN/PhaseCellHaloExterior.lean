module

public import IntegerMultBounds.NLogN.PhaseCellHaloNeighborhood

/-! Exterior recovery rows vanish away from the halo endpoints and ambient wrap guards. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

open PhaseCellMatrix

/-- A nonwrapping stencil that lies entirely outside the halo. -/
def haloExteriorAt (s band a b i : ℕ) : Bool :=
  decide (band ≤ i ∧ i+band < s ∧ (i+band < a ∨ b+band ≤ i))

def haloExterior (s band a b : ℕ) [NeZero s] : Finset (ZMod s) :=
  Finset.univ.filter (fun i => haloExteriorAt s band a b i.val = true)

def recoveryZeroRows (s t band a b : ℕ) [NeZero s] : Finset (ZMod s) :=
  haloInterior s t (2*band) a b ∪ haloExterior s band a b

variable {s t : ℕ} [NeZero s]

theorem haloExterior_stencil_disjoint (band a b : ℕ) (i : ZMod s)
    (hi : i ∈ haloExterior s band a b) {δ : ℤ} (hδ : δ ∈ spatialCouplingOffsets band) :
    i+(δ : ZMod s) ∉ haloVertices s a b := by
  have hi' : band ≤ i.val ∧ i.val+band < s ∧ (i.val+band < a ∨ b+band ≤ i.val) := by
    simpa [haloExterior,haloExteriorAt] using hi
  have hd := spatialCouplingOffsets_bounds band hδ
  let j := i+(δ : ZMod s)
  have hjval : (j.val : ℤ) = (i.val : ℤ)+δ := by
    have hj : j = (((i.val : ℤ)+δ : ℤ) : ZMod s) := by simp [j]
    rw [hj,ZMod.val_intCast,Int.emod_eq_of_lt (by omega) (by omega)]
  change j ∉ haloVertices s a b
  intro hj
  obtain ⟨ha,hb⟩ := (mem_haloVertices a b j).mp hj
  rcases hi'.2.2 with h | h <;> omega

theorem recoveryZeroRows_stencil_disjoint (hst : s ≤ t) (band a b : ℕ) (i : ZMod s)
    (hi : i ∈ recoveryZeroRows s t band a b) {δ : ℤ} (hδ : δ ∈ spatialCouplingOffsets band) :
    i+(δ : ZMod s) ∉ haloBoundary s t band a b := by
  rcases Finset.mem_union.mp hi with hdeep | hout
  · exact haloInterior_stencil_disjoint_boundary hst band a b i hdeep hδ
  · exact fun h => haloExterior_stencil_disjoint band a b i hout hδ (Finset.mem_sdiff.mp h).1

/-- Full recovery work is confined to enlarged phase/halo boundaries and four short guard strips. -/
theorem recovery_active_cover (band a b : ℕ) :
    Finset.univ \ recoveryZeroRows s t band a b ⊆
      (((haloBoundary s t (2*band) a b ∪ haloVertices s 0 band) ∪ haloVertices s (s-band) s) ∪
        haloVertices s (a-band) a) ∪ haloVertices s b (b+band) := by
  intro i hi
  have hzero := (Finset.mem_sdiff.mp hi).2
  by_contra hnot
  have hB : i ∉ haloBoundary s t (2*band) a b := by intro h; exact hnot (by simp [h])
  have h0 : i ∉ haloVertices s 0 band := by intro h; exact hnot (by simp [h])
  have hs : i ∉ haloVertices s (s-band) s := by intro h; exact hnot (by simp [h])
  have ha : i ∉ haloVertices s (a-band) a := by intro h; exact hnot (by simp [h])
  have hb : i ∉ haloVertices s b (b+band) := by intro h; exact hnot (by simp [h])
  have hdeep : i ∉ haloInterior s t (2*band) a b := by intro h; exact hzero (Finset.mem_union.mpr (Or.inl h))
  have hV : i ∉ haloVertices s a b := by intro h; exact hB (Finset.mem_sdiff.mpr ⟨h,hdeep⟩)
  have hiS := ZMod.val_lt i
  simp only [mem_haloVertices] at h0 hs ha hb hV
  have hext : i ∈ haloExterior s band a b := by
    simp only [haloExterior,Finset.mem_filter,Finset.mem_univ,true_and,haloExteriorAt,decide_eq_true_eq]
    omega
  exact hzero (Finset.mem_union.mpr (Or.inr hext))

theorem recovery_active_card_le (hst : s < t) (band a b : ℕ) :
    (Finset.univ \ recoveryZeroRows s t band a b).card ≤
      haloBoundaryCountBound s t (2*band) a b+4*band := by
  have hc := Finset.card_le_card (recovery_active_cover (s := s) (t := t) band a b)
  have hB := haloBoundary_card_bound hst (2*band) a b
  have h0 := haloVertices_card_le s 0 band
  have hs := haloVertices_card_le s (s-band) s
  have ha := haloVertices_card_le s (a-band) a
  have hb := haloVertices_card_le s b (b+band)
  have h1 := Finset.card_union_le (haloBoundary s t (2*band) a b) (haloVertices s 0 band)
  have h2 := Finset.card_union_le (haloBoundary s t (2*band) a b ∪ haloVertices s 0 band) (haloVertices s (s-band) s)
  have h3 := Finset.card_union_le ((haloBoundary s t (2*band) a b ∪ haloVertices s 0 band) ∪ haloVertices s (s-band) s) (haloVertices s (a-band) a)
  have h4 := Finset.card_union_le (((haloBoundary s t (2*band) a b ∪ haloVertices s 0 band) ∪ haloVertices s (s-band) s) ∪ haloVertices s (a-band) a) (haloVertices s b (b+band))
  omega

theorem haloExterior_active_cover (band a b : ℕ) :
    Finset.univ \ haloExterior s band a b ⊆
      (haloVertices s (a-band) (b+band) ∪ haloVertices s 0 band) ∪ haloVertices s (s-band) s := by
  intro i hi
  have he := (Finset.mem_sdiff.mp hi).2
  by_contra hnot
  have hmid : i ∉ haloVertices s (a-band) (b+band) := by intro h; exact hnot (by simp [h])
  have h0 : i ∉ haloVertices s 0 band := by intro h; exact hnot (by simp [h])
  have hs : i ∉ haloVertices s (s-band) s := by intro h; exact hnot (by simp [h])
  apply he
  have hiS := ZMod.val_lt i
  simp only [mem_haloVertices] at hmid h0 hs
  simp only [haloExterior,Finset.mem_filter,Finset.mem_univ,true_and,haloExteriorAt,decide_eq_true_eq]
  omega

theorem haloExterior_active_card_le (band a b : ℕ) :
    (Finset.univ \ haloExterior s band a b).card ≤ b-a+4*band := by
  have hc := Finset.card_le_card (haloExterior_active_cover (s := s) band a b)
  have hm := haloVertices_card_le s (a-band) (b+band)
  have h0 := haloVertices_card_le s 0 band
  have hs := haloVertices_card_le s (s-band) s
  have h1 := Finset.card_union_le (haloVertices s (a-band) (b+band)) (haloVertices s 0 band)
  have h2 := Finset.card_union_le (haloVertices s (a-band) (b+band) ∪ haloVertices s 0 band) (haloVertices s (s-band) s)
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
