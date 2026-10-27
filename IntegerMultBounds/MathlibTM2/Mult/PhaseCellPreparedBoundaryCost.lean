module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedBoundarySolve
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundaryCount

/-! Repeated prepared boundary work is charged by rows times bandwidth, independently of factor setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def preparedBoundaryRowCost (w W : ℕ) : ℕ :=
  (2*W+1)*rmulCost w+92*W*w+120*W+108*w+172

theorem preparedBoundarySolveCost_eq (w N W : ℕ) :
    preparedBoundarySolveCost w N W = N*preparedBoundaryRowCost w W+12*W*w+50 := by
  dsimp [preparedBoundarySolveCost,preparedBoundaryRowCost,bandLinePassCost,bandFwdStepCost]
  ring

theorem preparedBoundarySolveCost_mono_rows (w W : ℕ) {N M : ℕ} (hNM : N ≤ M) :
    preparedBoundarySolveCost w N W ≤ preparedBoundarySolveCost w M W := by
  rw [preparedBoundarySolveCost_eq,preparedBoundarySolveCost_eq]
  simp only [Nat.add_assoc]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right (preparedBoundaryRowCost w W) hNM) _

theorem preparedBoundaryRowCost_le (w W : ℕ) (hW : 1 ≤ W) :
    preparedBoundaryRowCost w W ≤ 300*W*(rmulCost w+w+1) := by
  have hm := Nat.mul_le_mul_right (rmulCost w) hW
  have hw := Nat.mul_le_mul_right w hW
  dsimp [preparedBoundaryRowCost]
  nlinarith only [hm,hw,hW,Nat.zero_le (W*rmulCost w),Nat.zero_le (W*w)]

theorem preparedBoundarySolveCost_le (w N W : ℕ) (hW : 1 ≤ W) :
    preparedBoundarySolveCost w N W ≤ 400*(N+1)*W*(rmulCost w+w+1) := by
  have hrow := preparedBoundaryRowCost_le w W hW
  have htail : 12*W*w+50 ≤ 62*W*(rmulCost w+w+1) := by
    nlinarith only [hW,Nat.zero_le (W*rmulCost w),Nat.zero_le (W*w)]
  rw [preparedBoundarySolveCost_eq]
  rw [Nat.add_assoc]
  calc
    _ ≤ N*(300*W*(rmulCost w+w+1))+62*W*(rmulCost w+w+1) :=
      Nat.add_le_add (Nat.mul_le_mul_left N hrow) htail
    _ = (300*N+62)*W*(rmulCost w+w+1) := by ring
    _ ≤ 400*(N+1)*W*(rmulCost w+w+1) := by gcongr <;> omega

theorem preparedHaloBoundarySolveCost_le {s t : ℕ} [NeZero s] (hst : s < t)
    (w band a b : ℕ) :
    preparedBoundarySolveCost w (haloBoundary s t band a b).card (12*band+1) ≤
      400*(min (b-a) (2*band*(t-s+2))+1)*(12*band+1)*(rmulCost w+w+1) := by
  have hrows := haloBoundary_card_bound hst band a b
  exact (preparedBoundarySolveCost_mono_rows w (12*band+1) hrows).trans
    (preparedBoundarySolveCost_le w _ (12*band+1) (by omega))

theorem preparedBoundarySolveCost_replicas (w N W replicas : ℕ) :
    replicas*preparedBoundarySolveCost w N W =
      (replicas*N)*preparedBoundaryRowCost w W+replicas*(12*W*w+50) := by
  rw [preparedBoundarySolveCost_eq]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
