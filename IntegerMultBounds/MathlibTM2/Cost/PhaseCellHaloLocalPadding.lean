module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloRingSizing
public import IntegerMultBounds.NLogN.PhaseCellHaloPhaseRange
public import IntegerMultBounds.NLogN.PhaseCellHaloScheduleCost

/-! Local phase padding pays halo span plus endpoint slack, including all short
clipped cells. No lower bound on an individual row length is needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix
open scoped BigOperators

theorem haloPhaseCount_paddedVolume_le {s t : ℕ} (hs : 0 < s)
    (hgap : t-s ≤ s) (a b : ℕ) (hab : a ≤ b) :
    haloPhaseCount s t a b * 2^haloInverseRingLog s t ≤ 8*(b-a)+8*(s/(t-s)+1) := by
  let k := s/(t-s)+1
  have hc := haloPhaseCount_scaled_le (t := t) hs a b hab
  have hd := Nat.mul_div_le s (t-s)
  have hk : (t-s)*k ≤ 2*s := by dsimp only [k]; nlinarith only [hd,hgap]
  have hck := Nat.mul_le_mul_right k hc
  have hks := Nat.mul_le_mul_right (2*(b-a)) hk
  have hscaled : s*(haloPhaseCount s t a b*k) ≤ s*(2*(b-a)+2*k) := by
    nlinarith only [hck,hks]
  have hcount := le_of_mul_le_mul_left hscaled hs
  have hr := Nat.mul_le_mul_left (haloPhaseCount s t a b) (haloInverseRingSize_le s t)
  dsimp only [k] at hcount
  nlinarith only [hr,hcount]

theorem haloLengthKeys_cell_count_local {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b : ℕ) :
    ((haloLengthKeys s t band a b).map (fun L => (haloLengthGroup s t band a b L).length)).sum ≤
      haloPhaseCount s t a b := by
  let phases := (Finset.range (t-s+1)).filter (fun phase => 0 < haloLength s t band a b phase)
  have hmaps : ∀ phase ∈ phases, haloLength s t band a b phase ∈ (haloLengthKeys s t band a b).toFinset := by
    intro phase hp
    obtain ⟨hr,hpos⟩ := Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr (haloLengthKeys_cover hst band a b phase
      ((mem_haloCellPhases s t band a b phase).mpr ⟨by have hh := Finset.mem_range.mp hr; omega,hpos⟩))
  rw [← List.sum_toFinset _ (haloLengthKeys_nodup s t band a b)]
  calc
    _ = ∑ L ∈ (haloLengthKeys s t band a b).toFinset,
        (phases.filter (fun phase => haloLength s t band a b phase = L)).card := by
      apply Finset.sum_congr rfl
      intro L hL
      exact (haloLengthGroup_fiber s t band a b L
        (of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp hL)).2)).symm
    _ = phases.card := by
      simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] using
        Finset.sum_fiberwise_of_maps_to' hmaps (fun _ : ℕ => (1 : ℕ))
    _ ≤ (Finset.Icc (naturalPhase s t a) (naturalPhase s t b)).card := by
      apply Finset.card_le_card
      intro phase hp
      exact Finset.mem_Icc.mpr (haloCellPhase_bounds hst band a b phase (Finset.mem_filter.mp hp).2)
    _ = haloPhaseCount s t a b := by
      simp only [Nat.card_Icc,haloPhaseCount,haloPhaseStart]

/-- Summed ring padding is local even for arbitrarily short endpoint classes. -/
theorem haloLengthKeys_paddedVolume_le {s t : ℕ} [NeZero s] (hst : s < t)
    (hgap : t-s ≤ s) (band a b : ℕ) (hab : a ≤ b) :
    ((haloLengthKeys s t band a b).map (fun L =>
      (haloLengthGroup s t band a b L).length*(L+2^haloInverseRingLog s t))).sum ≤
        (haloInterior s t band a b).card+8*(b-a)+8*(s/(t-s)+1) := by
  have hc := haloLengthKeys_cell_count_local hst band a b
  have hp := haloPhaseCount_paddedVolume_le (NeZero.pos s) hgap a b hab
  have hm := Nat.mul_le_mul_right (2^haloInverseRingLog s t) hc
  have hsplit (xs : List ℕ) :
      (xs.map (fun L => (haloLengthGroup s t band a b L).length*(L+2^haloInverseRingLog s t))).sum =
      (xs.map (fun L => (haloLengthGroup s t band a b L).length*L)).sum+
        (xs.map (fun L => (haloLengthGroup s t band a b L).length)).sum*2^haloInverseRingLog s t := by
    induction xs with
    | nil => simp
    | cons L xs ih => simp only [List.map_cons,List.sum_cons,ih]; ring
  rw [hsplit,haloLengthKeys_volume hst band a b]
  omega

/-- All equal-length batches together pay local padding and at most six span scans. -/
theorem haloLengthKeys_localTraffic_le {s t : ℕ} [NeZero s] (hst : s < t)
    (hgap : t-s ≤ s) (band a b N w : ℕ) (hab : a ≤ b) :
    ((haloLengthKeys s t band a b).map (fun L =>
      N*((haloLengthGroup s t band a b L).length*(L+2^haloInverseRingLog s t)*w+(b-a)*w+1))).sum ≤
        N*(((haloInterior s t band a b).card+8*(b-a)+8*(s/(t-s)+1))*w+
          6*((b-a)*w+1)) := by
  have hv := haloLengthKeys_paddedVolume_le hst hgap band a b hab
  have hk := haloLengthKeys_length_le s t band a b
  have hsum (xs : List ℕ) :
      (xs.map (fun L => N*((haloLengthGroup s t band a b L).length*(L+2^haloInverseRingLog s t)*w+
        (b-a)*w+1))).sum =
      N*((xs.map (fun L => (haloLengthGroup s t band a b L).length*(L+2^haloInverseRingLog s t))).sum*w+
        xs.length*((b-a)*w+1)) := by
    induction xs with
    | nil => simp
    | cons L xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; ring
  rw [hsum]
  exact Nat.mul_le_mul_left N (Nat.add_le_add (Nat.mul_le_mul_right w hv)
    (Nat.mul_le_mul_right _ hk))

end IntegerMultBounds.MathlibTM2.Cost
