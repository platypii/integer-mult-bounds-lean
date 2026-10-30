module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProtectedHaloScatter
public import IntegerMultBounds.NLogN.PhaseCellHaloLengthKeys

/-! Publication costs aggregate over the generated bounded list of length keys.
Sweeping once per key remains linear in the ambient encoded line volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The exact scatter bills, with the ordinary counted-loop overhead. -/
def haloPublicationScheduleCost (s t band a b w : ℕ) (keys : List ℕ) : ℕ :=
  (keys.map (fun L => haloScatterCost s t band a b L w+3)).sum+2

theorem haloPublicationScheduleCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b w : ℕ) (hw : 1 ≤ w) (keys : List ℕ) :
    haloPublicationScheduleCost s t band a b w keys ≤ keys.length*(35*s*w+9)+2 := by
  unfold haloPublicationScheduleCost
  suffices (keys.map (fun L => haloScatterCost s t band a b L w+3)).sum ≤
      keys.length*(35*s*w+9) by omega
  induction keys with
  | nil => simp
  | cons L keys ih =>
    have hL := haloScatterCost_le hst band a b L w hw
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- All generated length classes together require at most six forward sweeps. -/
theorem selectedHaloPublicationScheduleCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (band a b w : ℕ) (hw : 1 ≤ w) :
    haloPublicationScheduleCost s t band a b w (haloLengthKeys s t band a b) ≤ 210*s*w+56 := by
  have hcost := haloPublicationScheduleCost_le hst band a b w hw (haloLengthKeys s t band a b)
  have hkeys := haloLengthKeys_length_le s t band a b
  have hm := Nat.mul_le_mul_right (35*s*w+9) hkeys
  nlinarith only [hcost,hm]

/-- Includes each protected caller's window-counter construction and release,
as well as the outer counted-loop overhead. -/
def protectedHaloPublicationScheduleCost (s w : ℕ) (keys : List ℕ) : ℕ :=
  keys.length*(54*s*w+18)+2

theorem selectedProtectedHaloPublicationScheduleCost_le (s t band a b w : ℕ) :
    protectedHaloPublicationScheduleCost s w (haloLengthKeys s t band a b) ≤ 324*s*w+110 := by
  have hkeys := haloLengthKeys_length_le s t band a b
  unfold protectedHaloPublicationScheduleCost
  have hm := Nat.mul_le_mul_right (54*s*w+18) hkeys
  nlinarith only [hm]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
