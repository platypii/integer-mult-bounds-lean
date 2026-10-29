module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroupAccuracy

/-! Every generated cell group writes only halo-interior words. Boundary words
therefore have an exact structural frame, independent of numerical accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement

theorem haloPackedOffsets_interior {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b L r j : ℕ) (hb : b ≤ s) (hr : r ∈ haloPackedOffsets s t band a b L)
    (hj : r ≤ j) (hjL : j < r+L) :
    ((a+j : ℕ) : ZMod s) ∈ haloInterior s t band a b := by
  obtain ⟨start,hstart,rfl⟩ := List.mem_map.mp hr
  have hbounds := haloOrigins_bounds s t band a b L start hstart
  obtain ⟨phase,hphase,rfl⟩ := List.mem_map.mp hstart
  obtain ⟨_,hpos,hlen⟩ := (mem_haloLengthGroup s t band a b L phase).mp hphase
  have hjs : a+j < s := by omega
  apply ((haloInterior_phase_iff hst band a b phase _).mpr ?_).1
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt hjs]
  unfold haloLength at hlen
  omega

/-- One group publication leaves each complete word outside the interior intact. -/
theorem haloGroup_scatter_off_interior_word {α : Type*} {s t : ℕ} [NeZero s]
    (hst : s < t) (band a b L w : ℕ) (hb : b ≤ s)
    (E X tail : List α) (hE : E.length = (b-a)*w)
    (hX : (haloPackedOffsets s t band a b L).length*(L*w) ≤ X.length)
    (j : ℕ) (hj : j < b-a) (hoff : ((a+j : ℕ) : ZMod s) ∉ haloInterior s t band a b) :
    (((scatterRows (L*w) E X (packedCellGaps L w (haloPackedOffsets s t band a b L)))++tail).drop
      (j*w)).take w = ((E++tail).drop (j*w)).take w := by
  let ps := (haloPackedOffsets s t band a b L).map (·*w)
  have hd : ps.Pairwise (fun p q => p+L*w ≤ q) :=
    packedCell_offsets_disjoint L w _ (haloPackedOffsets_disjoint s t band a b L)
  have hf : ∀ p ∈ ps, p+L*w ≤ E.length := by
    intro p hp
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp
    rw [hE,← Nat.add_mul]
    exact Nat.mul_le_mul_right w (haloPackedOffsets_fit s t band a b L r hr)
  have hx : ps.length*(L*w) ≤ X.length := by simpa [ps] using hX
  have hfits := windowGaps_fits (L*w) 0 ps E (fun _ _ => Nat.zero_le _) hd hf
  have hlen : (scatterRows (L*w) E X (windowGaps (L*w) 0 ps)).length = E.length :=
    length_scatterRows _ _ _ _ hfits (by simpa using hx)
  have hbound : j*w+w ≤ E.length := by
    rw [hE]
    simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right w (show j+1 ≤ b-a by omega)
  have he := scatterRows_slice_off (L*w) ps E X hd hf hx (j*w) w (by
    intro n hn
    have hn' : n < (haloPackedOffsets s t band a b L).length := by simpa [ps] using hn
    let r := (haloPackedOffsets s t band a b L)[n]
    have hr : r ∈ haloPackedOffsets s t band a b L := List.getElem_mem hn'
    have hsep : j+1 ≤ r ∨ r+L ≤ j := by
      by_contra hh
      have hstart : r ≤ j := by omega
      have hstop : j < r+L := by omega
      exact hoff (haloPackedOffsets_interior hst band a b L r j hb hr hstart hstop)
    simp only [ps,List.getElem_map]
    change j*w+w ≤ r*w ∨ r*w+L*w ≤ j*w
    rcases hsep with hs | hs
    · left; simpa only [Nat.add_mul,Nat.one_mul] using Nat.mul_le_mul_right w hs
    · right; simpa only [Nat.add_mul] using Nat.mul_le_mul_right w hs)
  change (((scatterRows (L*w) E X (windowGaps (L*w) 0 ps))++tail).drop (j*w)).take w = _
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop,hlen]; omega),
    List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
  exact he

/-- Exact preservation of local words outside the halo interior. -/
def PackedHaloWordFrame {α : Type*} (s t band a b w : ℕ) [NeZero s]
    (before after : List α) : Prop :=
  ∀ j < b-a, ((a+j : ℕ) : ZMod s) ∉ haloInterior s t band a b →
    (after.drop (j*w)).take w = (before.drop (j*w)).take w

theorem PackedHaloWordFrame.refl {α : Type*} (s t band a b w : ℕ) [NeZero s] (xs : List α) :
    PackedHaloWordFrame s t band a b w xs xs := fun _ _ _ => rfl

theorem PackedHaloWordFrame.trans {α : Type*} {s t band a b w : ℕ} [NeZero s]
    {xs ys zs : List α} (h₂ : PackedHaloWordFrame s t band a b w ys zs)
    (h₁ : PackedHaloWordFrame s t band a b w xs ys) : PackedHaloWordFrame s t band a b w xs zs :=
  fun j hj hi => (h₂ j hj hi).trans (h₁ j hj hi)

/-- The word frame also preserves the actual decoded local read. -/
theorem PackedHaloWordFrame.read {A s t band a b w q : ℕ} [NeZero s]
    {before after : List (Fin (A+4))} (h : PackedHaloWordFrame s t band a b w before after)
    (i : ZMod s) (ha : a ≤ i.val) (hb : i.val < b)
    (hi : i ∉ haloInterior s t band a b) :
    packedIntervalRead q w a after i = packedIntervalRead q w a before i := by
  have hj : i.val-a < b-a := by omega
  have hoff : ((a+(i.val-a) : ℕ) : ZMod s) ∉ haloInterior s t band a b := by
    simpa only [Nat.add_sub_of_le ha,ZMod.natCast_zmod_val] using hi
  simp only [packedIntervalRead]
  rw [h (i.val-a) hj hoff]

/-- Combine interior accuracy with the retained boundary's accuracy directly on
physical reads of the final buffer. -/
theorem PackedHaloWordFrame.error {A s t band a b w q : ℕ} [NeZero s]
    {before after : List (Fin (A+4))} (h : PackedHaloWordFrame s t band a b w before after)
    (hB : ∀ i ∈ haloBoundary s t band a b, a ≤ i.val ∧ i.val < b)
    (x : ZMod s → ℝ) (η ε : ℝ)
    (hI : PhaseCellInterface.ErrorOn (haloInterior s t band a b)
      (fun i => (packedIntervalRead q w a after i).re) x η)
    (hboundary : PhaseCellInterface.ErrorOn (haloBoundary s t band a b)
      (fun i => (packedIntervalRead q w a before i).re) x ε) :
    PhaseCellInterface.ErrorOn (haloVertices s a b)
      (fun i => (packedIntervalRead q w a after i).re) x (max η ε) := by
  intro i hi
  have hm : i ∈ haloInterior s t band a b ∪ haloBoundary s t band a b := by
    rwa [haloInterior_union_boundary]
  by_cases hiI : i ∈ haloInterior s t band a b
  · exact (hI i hiI).trans (le_max_left _ _)
  · have hiB := (Finset.mem_union.mp hm).resolve_left hiI
    dsimp only
    rw [h.read i (hB i hiB).1 (hB i hiB).2 hiI]
    exact (hboundary i hiB).trans (le_max_right _ _)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
