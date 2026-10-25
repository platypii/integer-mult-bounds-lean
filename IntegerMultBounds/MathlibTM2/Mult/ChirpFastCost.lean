module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupCost

/-! # Linear coefficient-volume bounds for the retained forward caller -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.Spec.SignedRingProduct

/-- The least power of two covering a seven-window convolution is below fourteen windows. -/
theorem chirpRingSize_le (m : ℕ) (hm : 1 ≤ m) : 2 ^ Nat.clog 2 (7 * m) ≤ 14 * m := by
  have hn : 1 < 7 * m := by omega
  have hc := Nat.clog_pos (by decide : 1 < 2) hn
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hn
  have he : Nat.clog 2 (7 * m) = (Nat.clog 2 (7 * m)).pred + 1 :=
    (Nat.succ_pred_eq_of_pos hc).symm
  rw [he, pow_succ]
  omega

/-- Padding the final block increases total block volume by at most one window. -/
theorem chirpBlockCount_volume (t m : ℕ) (hm : 1 ≤ m) :
    chirpBlockCount t m ≤ t + m ∧ chirpBlockCount t m * (3 * m + 1) ≤ 4 * (t + m) := by
  have hv := chirpBlockCount_mul_le t m
  have hn : chirpBlockCount t m ≤ chirpBlockCount t m * m := Nat.le_mul_of_pos_right _ hm
  constructor <;> nlinarith only [hv, hn]

/-- One line's short-product fixed cost, including every shared header and cleanup. -/
def chirpProductFixedBound (p l w m : ℕ) : ℕ :=
  rpFixCost p l w + 52 * (2 ^ l * w) + 18 * m * w + 37 * m + 12 * w + 27 * l +
    ldrHeaderCost p l w + 2 * (header p (2 ^ l) w).length + 100

/-- Reuse the existing S1 bound: all non-ring work is linear in the padded coefficient volume. -/
theorem chirpBatchProductCost_le_volume (p l w m M : ℕ) (hw : 1 ≤ w) (hm : 1 ≤ m)
    (hlo : 7 * m ≤ 2 ^ l) (hhi : 2 ^ l ≤ 14 * m) :
    chirpBatchProductCost p l w m M ≤ chirpProductFixedBound p l w m +
      M * rpRecBound p l w + 800 * (M * m) * (w + 1) := by
  have hrw := Nat.mul_le_mul_right w hhi
  have hrec : 52 * (2 ^ l * w) + 38 * m * w + 19 * m + 73 ≤ 800 * m * (w + 1) := by
    nlinarith only [hrw, hm, Nat.zero_le (m * w)]
  have h := chirpBatchProductCost_le p l w m M hw hm hlo
  have h' : chirpBatchProductCost p l w m M ≤
      M * (rpRecBound p l w + (52 * (2 ^ l * w) + 38 * m * w + 19 * m + 73)) +
        chirpProductFixedBound p l w m := by
    simpa only [chirpProductFixedBound, Nat.add_assoc] using h
  calc
    _ ≤ M * (rpRecBound p l w + 800 * m * (w + 1)) + chirpProductFixedBound p l w m :=
      h'.trans (Nat.add_le_add_right (Nat.mul_le_mul_left M (Nat.add_le_add_left hrec _)) _)
    _ = _ := by ring

/-- Shared-control gathering is linear in source/output volume, plus fixed scalar arithmetic. -/
theorem chirpRawGatherSharedCost_le (W e s t m w : ℕ) (hs : 0 < s) (hst : s ≤ t)
    (ht : 0 < t) (hm : 1 ≤ m) :
    chirpRawGatherWithCost true W e s t m w (chirpBlockCount t m) ≤
      25 * IntegerMultBounds.MathlibTM2.Fast.TableVM.tblC W e + 55 * W +
        300 * (s + t + m + 1) * (w + 1) + 100 := by
  let T := s + t + m + 1
  let M := chirpBlockCount t m
  have hvol := chirpBlockCount_volume t m hm
  have hM : M ≤ T := by dsimp [M, T]; omega
  have hAw : M * (3 * m + 1) * w ≤ 4 * T * w :=
    Nat.mul_le_mul_right w (hvol.2.trans (by dsimp [T]; omega))
  have hCs : chirpPeriods s m * s ≤ 3 * T := by
    have h := chirpPeriods_overshoot hs m
    dsimp [T]
    omega
  have hC : chirpPeriods s m ≤ 3 * T :=
    (Nat.le_mul_of_pos_right _ hs).trans hCs
  have hCsw := Nat.mul_le_mul_right w hCs
  have hsw : s * w ≤ T * w := Nat.mul_le_mul_right w (by dsimp [T]; omega)
  have hlong : (s + 3 * m) * w ≤ 3 * T * w := Nat.mul_le_mul_right w (by dsimp [T]; omega)
  have hrow : (3 * m + 1) * w ≤ 3 * T * w := Nat.mul_le_mul_right w (by dsimp [T]; omega)
  have hK : chirpCyclicCounterTotal s m w ≤ 10 * T * (w + 1) := by
    unfold chirpCyclicCounterTotal
    nlinarith only [hsw, hC, hlong, hrow, Nat.zero_le (T * w)]
  have hcopy : chirpRawCopyCost s m w ≤ 100 * T * (w + 1) + 38 := by
    unfold chirpRawCopyCost
    nlinarith only [hCsw, hC, hsw, hlong, Nat.zero_le (T * w)]
  have hcenter := chirpCenter_end_le hst ht (fun j hj => chirpBlock_valid ht hm hj)
  have hD : chirpCenter s t m M * w ≤ T * w :=
    Nat.mul_le_mul_right w (hcenter.trans (by dsimp [T]; omega))
  have hsweep : chirpGatherModeCost true W e s t m w M ≤ 100 * T * (w + 1) + 8 := by
    simp only [chirpGatherModeCost, ite_true]
    nlinarith only [hAw, hM, hD, Nat.zero_le (T * w)]
  unfold chirpRawGatherWithCost chirpRawSetupCost
  change _ ≤ 25 * _ + 55 * W + 300 * T * (w + 1) + 100
  nlinarith only [hK, hcopy, hsweep, hlong, Nat.zero_le (T * w)]

theorem chirpMakeXSetupCost_le_linear (W e s t m w : ℕ) (hm : 1 ≤ m) :
    chirpMakeXSetupCost W e t m w ≤ 18 * IntegerMultBounds.MathlibTM2.Fast.TableVM.tblC W e +
      33 * W + 4 * (s + t + m + 1) * rmulCost w + 300 * (s + t + m + 1) * (w + 1) + 44 := by
  let T := s + t + m + 1
  let M := chirpBlockCount t m
  have hv := chirpBlockCount_volume t m hm
  have hM : M ≤ T := by dsimp [M, T]; omega
  have hA : M * (3 * m + 1) ≤ 4 * T := hv.2.trans (by dsimp [T]; omega)
  have hAw := Nat.mul_le_mul_right w hA
  have hAR := Nat.mul_le_mul_right (rmulCost w) hA
  have hL : 3 * m + 1 ≤ 3 * T := by dsimp [T]; omega
  have hLw := Nat.mul_le_mul_right w hL
  have hK : M + (3 * m + 1) + (3 * m + 1) * w ≤ 7 * T * (w + 1) := by
    nlinarith only [hM, hL, hLw, Nat.zero_le (T * w)]
  have hX : chirpMakeXCost M m w ≤ 4 * T * rmulCost w + 200 * T * (w + 1) + 18 := by
    unfold chirpMakeXCost
    nlinarith only [hA, hAw, hAR, hM, Nat.zero_le (T * w)]
  unfold chirpMakeXSetupCost
  change _ ≤ 18 * _ + 33 * W + 4 * T * rmulCost w + 300 * T * (w + 1) + 44
  nlinarith only [hK, hX, Nat.zero_le (T * w)]

/-- Both output products, shifts, rounding and crop are linear in the retained coefficient count. -/
theorem chirpOutputCompleteCost_le_linear (N p q l Γ w t : ℕ)
    (hq : q ≤ w) (hl : l ≤ w) (hΓ : Γ ≤ w) (hwo : p + l + Γ + 5 ≤ w) :
    chirpOutputCompleteCost N p q l Γ w t ≤
      2 * N * rmulCost w + 200 * N * (w + 1) + 37 := by
  have hs : q - p ≤ w := (Nat.sub_le q p).trans hq
  have hd : w - (q - p) - (p + l + Γ + 5) ≤ w :=
    (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  have hshift : IntegerMultBounds.MathlibTM2.Node.topShiftWordCost w (q - p) (p + l + Γ + 5) ≤
      24 * w + 22 := by
    unfold IntegerMultBounds.MathlibTM2.Node.topShiftWordCost
    omega
  have hprod : chirpOutputProductsCost N l Γ w ≤ 2 * N * rmulCost w + 80 * N * (w + 1) + 20 := by
    have hlN := Nat.mul_le_mul_left N hl
    have hΓN := Nat.mul_le_mul_left N hΓ
    unfold chirpOutputProductsCost
    nlinarith only [hlN, hΓN, Nat.zero_le (N * w)]
  have hshiftN := Nat.mul_le_mul_left N hshift
  have hwoN := Nat.mul_le_mul_left N hwo
  have hmin : min t N * (p + l + Γ + 5) ≤ N * w := Nat.mul_le_mul (Nat.min_le_right _ _) hwo
  have hdrop : (N - t) * (p + l + Γ + 5) ≤ N * w := Nat.mul_le_mul (Nat.sub_le _ _) hwo
  have hfinish : chirpOutputFinishCost N p q l Γ w t ≤ 60 * N * (w + 1) + 12 := by
    unfold chirpOutputFinishCost
    nlinarith only [hshiftN, hwoN, hmin, hdrop, Nat.zero_le (N * w)]
  unfold chirpOutputCompleteCost
  nlinarith only [hprod, hfinish, Nat.zero_le (N * w)]

/-- Per-line scalar/header startup, independent of the source and output lengths. -/
def chirpLineFixedBound (W q l w m : ℕ) : ℕ :=
  61 * IntegerMultBounds.MathlibTM2.Fast.TableVM.tblC W w + 165 * W +
    8 * (q + l + w + 8 * m + 2) + chirpProductFixedBound (q + 1) l w m + 300

/-- Six pointwise products per coefficient-volume envelope and one short ring product per block. -/
def chirpForwardFastBound (W s t q l m w : ℕ) : ℕ :=
  chirpLineFixedBound W q l w m + chirpBlockCount t m * rpRecBound (q + 1) l w +
    6 * (s + t + m + 1) * rmulCost w + 2000 * (s + t + m + 1) * (w + 1)

/-- The executed retained-control line has no window-size factor in its pointwise work. -/
theorem chirpForwardUnitCost_le (W s t p q l Γ m w : ℕ)
    (hs : 0 < s) (hst : s ≤ t) (ht : 0 < t) (hm : 1 ≤ m) (hw : 1 ≤ w)
    (hlo : 7 * m ≤ 2 ^ l) (hhi : 2 ^ l ≤ 14 * m)
    (hq : q ≤ w) (hl : l ≤ w) (hΓ : Γ ≤ w) (hwo : p + l + Γ + 5 ≤ w) :
    chirpRawCorrelationModeCost true W w W w s t q l m w +
      chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t +
      18 * (s * w) + 4 * (t * (p + l + Γ + 5)) + 23 ≤
        chirpForwardFastBound W s t q l m w := by
  let T := s + t + m + 1
  let M := chirpBlockCount t m
  have hv := chirpBlockCount_volume t m hm
  have hM : M ≤ T := by dsimp [M, T]; omega
  have hN : M * m ≤ T := (chirpBlockCount_mul_le t m).trans (by dsimp [T]; omega)
  have hA : M * (3 * m + 1) * w ≤ 4 * T * w :=
    Nat.mul_le_mul_right w (hv.2.trans (by dsimp [T]; omega))
  have hraw := chirpRawGatherSharedCost_le W w s t m w hs hst ht hm
  have hx := chirpMakeXSetupCost_le_linear W w s t m w hm
  have hp := chirpBatchProductCost_le_volume (q + 1) l w m M hw hm hlo hhi
  have hPV := Nat.mul_le_mul_left 800 (Nat.mul_le_mul_right (w + 1) hN)
  have hdim : chirpDimensionBatchCost W w q t m w l ≤
      18 * IntegerMultBounds.MathlibTM2.Fast.TableVM.tblC W w + 77 * W +
      8 * (q + l + w + 8 * m + 2) + chirpProductFixedBound (q + 1) l w m +
      M * rpRecBound (q + 1) l w + 900 * T * (w + 1) + 58 := by
    unfold chirpDimensionBatchCost
    nlinarith only [hp, hPV, hM, Nat.zero_le (T * w)]
  have hout := chirpOutputCompleteCost_le_linear (M * m) p q l Γ w t hq hl hΓ hwo
  have hNR := Nat.mul_le_mul_right (rmulCost w) hN
  have hNW := Nat.mul_le_mul_right (w + 1) hN
  have hsw : s * w ≤ T * w := Nat.mul_le_mul_right w (by dsimp [T]; omega)
  have htw : t * (p + l + Γ + 5) ≤ T * w := Nat.mul_le_mul (by dsimp [T]; omega) hwo
  dsimp only [T, M] at *
  simp only [chirpRawCorrelationModeCost, chirpGatherFromDimensionsModeCost, ite_true,
    chirpStreamCorrelationCost, chirpForwardFastBound, chirpLineFixedBound]
  nlinarith only [hraw, hx, hdim, hout, hNR, hNW, hA, hsw, htw, Nat.zero_le (T * w)]

namespace LinePlacement

/-- The selected dimensions discharge every gate of the coefficient-volume estimate. -/
theorem selectedGroupUnitCost_le (s t α p : ℕ) [NeZero s] [NeZero t]
    (hst : s < t) (hα : 1 ≤ α) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
    selectedGroupUnitCost s t α p ≤ chirpForwardFastBound W s t q l m w := by
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  have hm : 1 ≤ m := Nat.mul_pos hα (Nat.succ_pos _)
  have hq : p ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  have he : selectedGroupUnitCost s t α p =
      chirpRawCorrelationModeCost true W w W w s t q l m w +
        chirpOutputCompleteCost (chirpBlockCount t m * m) p q l Γ w t +
        18 * (s * w) + 4 * (t * (p + l + Γ + 5)) + 23 := by
    dsimp only [selectedGroupUnitCost, groupLineBound, W, w, q, Γ, l, m]
    ring
  rw [he]
  exact chirpForwardUnitCost_le W s t p q l Γ m w (NeZero.pos s) hst.le (NeZero.pos t) hm
    (by dsimp [w]; omega) (chirpForwardRingLog_good p α) (chirpRingSize_le m hm)
    (by dsimp [w]; omega) (by dsimp [w]; omega) (by dsimp [w]; omega)
    (by dsimp [w]; omega)

/-- Shared setup/release plus linear coefficient work and one ring product per block per line. -/
def selectedGroupFastCost (s t α p N : ℕ) : ℕ :=
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  selectedGroupCost s t α p 0 + N * chirpForwardFastBound W s t q l m w

theorem selectedGroupCost_le_fast (s t α p N : ℕ) [NeZero s] [NeZero t]
    (hst : s < t) (hα : 1 ≤ α) :
    selectedGroupCost s t α p N ≤ selectedGroupFastCost s t α p N := by
  rw [selectedGroupCost_affine]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left N (selectedGroupUnitCost_le s t α p hst hα)) _

end LinePlacement

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
