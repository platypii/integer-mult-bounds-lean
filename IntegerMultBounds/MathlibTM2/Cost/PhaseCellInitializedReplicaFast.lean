module

public import IntegerMultBounds.MathlibTM2.Cost.AffineSchedule
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaHaloFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloLocalPadding
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaHaloLoop

/-! Sum the actual key-loop fast bills structurally. Both initialization and
empty candidates are paid; padding depends only on local halo volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s : ℕ}

def replicaHaloSymbolVolume (H : ReplicaHaloProblem s) (L : ℕ) :=
  (haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length*L*H.wordWidth

def replicaHaloCoordinateVolume (H : ReplicaHaloProblem s) (L : ℕ) :=
  (haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length*(L+2^H.l)+H.span+1

def replicaHaloLocalCoordinates (H : ReplicaHaloProblem s) :=
  (haloInterior s H.t H.band H.origin (H.origin+H.span)).card+8*H.span+8*(s/(H.t-s)+1)+6*(H.span+1)

def initializedReplicaHaloTime (H : ReplicaHaloProblem s) :=
  allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
    (placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
      (((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map (fun L => H.keyCost L+3)).sum+2))

def initializedReplicaHaloSharedTime (H : ReplicaHaloProblem s) :=
  10+placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
    (((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map (fun L => replicaHaloKeySharedTime H L+3)).sum+2)

theorem replicaHaloSchedule_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} (H : ReplicaHaloProblem s) (keys : List ℕ),
      (∀ L ∈ keys, 0 < L) → H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p →
      2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      ((keys.map (fun L => H.keyCost L+3)).sum : ℝ) ≤
        ((keys.map (fun L => replicaHaloKeySharedTime H L+3)).sum+
          (10*cV+19)*H.Fs.length*(keys.map (replicaHaloSymbolVolume H)).sum : ℕ)+
        (D*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))*((keys.map (replicaHaloCoordinateVolume H)).sum : ℕ) := by
  obtain ⟨D,hD,hfast⟩ := replicaHaloKey_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro s H keys hpositive hl hw hr hV
  apply sum_nat_cost_le_affine
  intro L hL
  have hh := hfast H L (hpositive L hL) hl hw hr hV
  dsimp only [replicaHaloSymbolVolume,replicaHaloCoordinateVolume]
  push_cast at hh ⊢
  nlinarith only [hh]

theorem replicaHaloSymbolVolume_sum [NeZero s] (H : ReplicaHaloProblem s) :
    ((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map (replicaHaloSymbolVolume H)).sum =
      (haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth := by
  unfold replicaHaloSymbolVolume
  rw [List.sum_map_mul_right,haloLengthKeys_volume H.s_lt_t]

theorem replicaHaloCoordinateVolume_sum_le_local [NeZero s] (H : ReplicaHaloProblem s)
    (hgap : H.t-s ≤ s) (hl : H.l = haloInverseRingLog s H.t) :
    ((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map (replicaHaloCoordinateVolume H)).sum ≤
      replicaHaloLocalCoordinates H := by
  have hh := haloLengthKeys_localTraffic_le H.s_lt_t hgap H.band H.origin (H.origin+H.span) 1 1 (by omega)
  unfold replicaHaloCoordinateVolume replicaHaloLocalCoordinates
  rw [hl]
  simpa only [Nat.one_mul,Nat.mul_one,Nat.add_sub_cancel_left] using hh

theorem initializedReplicaHalo_fast_le (cl cw cr cV : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {s : ℕ} [NeZero s] (H : ReplicaHaloProblem s),
      H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p → 2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (initializedReplicaHaloTime H : ℝ) ≤
        (initializedReplicaHaloSharedTime H+H.Fs.length*(10*(H.span*H.wordWidth)+9)+
          (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := replicaHaloSchedule_fast_le cl cw cr cV
  refine ⟨D,hD,?_⟩
  intro s _ H hl hw hr hV hgap hring
  have hc := hfast H (haloLengthKeys s H.t H.band H.origin (H.origin+H.span))
    (fun L hL => of_decide_eq_true (List.mem_filter.mp hL).2) hl hw hr hV
  rw [replicaHaloSymbolVolume_sum] at hc
  have hcoords : (((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
      (replicaHaloCoordinateVolume H)).sum : ℝ) ≤ replicaHaloLocalCoordinates H := by
    exact_mod_cast replicaHaloCoordinateVolume_sum_le_local H hgap hring
  have ht := mul_le_mul_of_nonneg_left hcoords
    (show (0 : ℝ) ≤ D*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ) by positivity)
  unfold initializedReplicaHaloTime initializedReplicaHaloSharedTime allocateZeroLineCost
  push_cast at hc ht ⊢
  nlinarith only [hc,ht]

end IntegerMultBounds.MathlibTM2.Cost
