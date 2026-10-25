module

public import IntegerMultBounds.MathlibTM2.Cost.ChirpLogGrowth
public import IntegerMultBounds.MathlibTM2.Cost.MatchConv
public import IntegerMultBounds.MathlibTM2.Mult.ChirpFastCost

/-! # The selected chirp ring records against the unchanged multiplication allowance -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Schedule
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- A selected ring record has O(m*p) packed bits and O(p^2) bits in absolute size. -/
theorem chirp_selected_packed_bounds (p α : ℕ) (hp : 1 ≤ p) (hα : 1 ≤ α) (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let N := wOf (q + 1) l w * 2 ^ l
    N ≤ 11984 * m * p ∧ N ≤ 23968 * p ^ 2 := by
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  have hm : 1 ≤ m := Nat.mul_pos hα (Nat.succ_pos _)
  have hr : 2 ^ l ≤ 14 * m := chirpRingSize_le m hm
  have hmUp : m ≤ 2 * p := chirpForwardWindow_le p α hαp
  have hwidths := chirpForwardWidths_le p α hp hαp
  have hl : l ≤ 10 * p := (chirpForwardRingLog_le p α hαp).trans (by omega)
  have hV : wOf (q + 1) l w ≤ 856 * p := by
    have hv := mt_cv_wOf_le (q + 1) l w (by omega)
    change q ≤ 83 * p ∧ w ≤ 125 * p ∧ _ at hwidths
    omega
  have hN : wOf (q + 1) l w * 2 ^ l ≤ 11984 * m * p := by
    calc
      _ ≤ (856 * p) * (14 * m) := Nat.mul_le_mul hV hr
      _ = _ := by ring
  refine ⟨hN, ?_⟩
  calc
    _ ≤ 11984 * m * p := hN
    _ ≤ 11984 * (2 * p) * p := Nat.mul_le_mul_right p (Nat.mul_le_mul_left 11984 hmUp)
    _ = _ := by ring

/-- Full ring-record cost, including format conversions, is O(m*M(p)) at selected dimensions. -/
theorem chirp_selected_rpRec_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α : ℕ, 1 ≤ p → 1 ≤ α → α ^ 2 ≤ p →
      let m := chirpForwardWindow p α
      let l := chirpForwardRingLog p α
      let Γ := chirpForwardGrowth p
      let q := chirpForwardPrecision p Γ l
      let w := q + l + Γ + 5
      (rpRecBound (q + 1) l w : ℝ) ≤ C * (m : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨C, hC, hring⟩ := chirp_ringBound_le 23968 11984
  refine ⟨3 * C + 1200000, by positivity, ?_⟩
  intro p α hp hα hαp
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let r := 2 ^ l
  let N := wOf (q + 1) l w * r
  have hm : 1 ≤ m := Nat.mul_pos hα (Nat.succ_pos _)
  have hr : r ≤ 14 * m := chirpRingSize_le m hm
  have hw : w ≤ 125 * p := (chirpForwardWidths_le p α hp hαp).2.1
  have hbounds := chirp_selected_packed_bounds p α hp hα hαp
  have hring' : (rpRingBound N : ℝ) ≤ C * (m : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) :=
    hring p m N hp hm hbounds.1 hbounds.2
  have hrw : r * w ≤ 1750 * m * p := by
    calc
      _ ≤ (14 * m) * (125 * p) := Nat.mul_le_mul hr hw
      _ = _ := by ring
  have hmp : m ≤ m * p := Nat.le_mul_of_pos_right _ hp
  have hmp1 : 1 ≤ m * p := Nat.mul_pos hm hp
  have hformat : 640 * (r * w) + 1200 * r + 612 ≤ 1200000 * m * p := by
    nlinarith only [hrw, hr, hmp, hmp1, Nat.zero_le (m * p)]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ) ^ (129 / 128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hformat' : 640 * ((r : ℝ) * w) + 1200 * (r : ℝ) + 612 ≤
      1200000 * (m : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
    calc
      _ ≤ 1200000 * (m : ℝ) * p := by exact_mod_cast hformat
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (by positivity)
  have hcast (S R w : ℕ) : ((3 * (S + R * (180 * w + 400) + 204) + 100 * (R * w) : ℕ) : ℝ) =
      3 * (S : ℝ) + (640 * ((R : ℝ) * w) + 1200 * (R : ℝ) + 612) := by push_cast; ring
  change ((3 * (rpRingBound N + r * (180 * w + 400) + 204) + 100 * (r * w) : ℕ) : ℝ) ≤ _
  rw [hcast]
  calc
    _ ≤ 3 * (C * (m : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ)) +
        1200000 * (m : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hring' (by norm_num)) hformat'
    _ = _ := by ring

/-- All repeated arithmetic and tape work matches M(p), apart from fixed per-line startup. -/
theorem chirp_selected_work_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α s t W : ℕ, 1 ≤ p → 1 ≤ α → α ^ 2 ≤ p →
      let m := chirpForwardWindow p α
      let l := chirpForwardRingLog p α
      let Γ := chirpForwardGrowth p
      let q := chirpForwardPrecision p Γ l
      let w := q + l + Γ + 5
      (chirpForwardFastBound W s t q l m w : ℝ) ≤
        (chirpLineFixedBound W q l w m : ℝ) +
          C * ((s + t + m + 1 : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨CR, hCR, hRec⟩ := chirp_selected_rpRec_le
  obtain ⟨CM, hCM, hMul⟩ := chirp_rmul_le 125
  refine ⟨CR + 6 * CM + 252000, by positivity, ?_⟩
  intro p α s t W hp hα hαp
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let M := chirpBlockCount t m
  let T := s + t + m + 1
  have hw125 : w ≤ 125 * p := (chirpForwardWidths_le p α hp hαp).2.1
  have hw1 : 1 ≤ w := by dsimp [w]; omega
  have hrec : (rpRecBound (q + 1) l w : ℝ) ≤ CR * (m : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) :=
    hRec p α hp hα hαp
  have hpoint := hMul p w hp hw1 hw125
  have hNm : M * m ≤ T := (chirpBlockCount_mul_le t m).trans (by dsimp [T]; omega)
  have hNm' : ((M * m : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hNm
  have hMRec : (M : ℝ) * (rpRecBound (q + 1) l w : ℝ) ≤
      CR * (T : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
    calc
      _ ≤ (M : ℝ) * (CR * (m : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ)) :=
        mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg _)
      _ = CR * ((M * m : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNm' hCR) (by positivity)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hpPow : (p : ℝ) ≤ (p : ℝ) ^ (129 / 128 : ℝ) :=
    Real.self_le_rpow_of_one_le hp1 (by norm_num)
  have hwPlus : w + 1 ≤ 126 * p := by omega
  have hwPow : (w : ℝ) + 1 ≤ 126 * (p : ℝ) ^ (129 / 128 : ℝ) := by
    calc
      _ ≤ 126 * (p : ℝ) := by exact_mod_cast hwPlus
      _ ≤ _ := mul_le_mul_of_nonneg_left hpPow (by norm_num)
  have hPoint := mul_le_mul_of_nonneg_left hpoint (show (0 : ℝ) ≤ 6 * (T : ℝ) by positivity)
  have hLinear := mul_le_mul_of_nonneg_left hwPow (show (0 : ℝ) ≤ 2000 * (T : ℝ) by positivity)
  have hcast (F M R T S w : ℕ) : ((F + M * R + 6 * T * S + 2000 * T * (w + 1) : ℕ) : ℝ) =
      (F : ℝ) + (M : ℝ) * R + 6 * (T : ℝ) * S + 2000 * (T : ℝ) * ((w : ℝ) + 1) := by
    push_cast
    ring
  change ((chirpLineFixedBound W q l w m + M * rpRecBound (q + 1) l w +
    6 * T * rmulCost w + 2000 * T * (w + 1) : ℕ) : ℝ) ≤ _
  rw [hcast]
  calc
    _ ≤ (chirpLineFixedBound W q l w m : ℝ) + CR * (T : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) +
        6 * (T : ℝ) * (CM * (p : ℝ) ^ (129 / 128 : ℝ)) +
        2000 * (T : ℝ) * (126 * (p : ℝ) ^ (129 / 128 : ℝ)) :=
      add_le_add (add_le_add (add_le_add le_rfl hMRec) hPoint) hLinear
    _ = _ := by ring

/-- The closed caller's fast budget, with a uniform multiplier constant and explicit startup. -/
theorem chirp_selected_group_work_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α s t N : ℕ, 1 ≤ p → 1 ≤ α → α ^ 2 ≤ p →
      let m := chirpForwardWindow p α
      let l := chirpForwardRingLog p α
      let Γ := chirpForwardGrowth p
      let q := chirpForwardPrecision p Γ l
      let w := q + l + Γ + 5
      let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
      (LinePlacement.selectedGroupFastCost s t α p N : ℝ) ≤
        (LinePlacement.selectedGroupCost s t α p 0 : ℝ) +
          (N : ℝ) * (chirpLineFixedBound W q l w m : ℝ) +
          C * (N : ℝ) * ((s + t + m + 1 : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨C, hC, hwork⟩ := chirp_selected_work_le
  refine ⟨C, hC, ?_⟩
  intro p α s t N hp hα hαp
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  have h := hwork p α s t W hp hα hαp
  have hN := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)
  have hcast (S N K : ℕ) : ((S + N * K : ℕ) : ℝ) = (S : ℝ) + (N : ℝ) * K := by push_cast; rfl
  change ((LinePlacement.selectedGroupCost s t α p 0 + N * chirpForwardFastBound W s t q l m w : ℕ) : ℝ) ≤ _
  rw [hcast]
  calc
    _ ≤ (LinePlacement.selectedGroupCost s t α p 0 : ℝ) +
        (N : ℝ) * ((chirpLineFixedBound W q l w m : ℝ) +
          C * ((s + t + m + 1 : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ)) := add_le_add le_rfl hN
    _ = _ := by ring

/-- Fixed short-product setup is quadratic in precision, uniformly in the window. -/
theorem chirp_product_fixed_quadratic {p a l w m : ℕ}
    (hp : 1 ≤ p) (ha : 1 ≤ a) (haUp : a ≤ 84 * p) (hl : l ≤ a)
    (hlUp : l ≤ 10 * p) (hw : w ≤ 125 * p) (hpa : p ≤ a)
    (hm : m ≤ 2 * p) (hr : 2 ^ l ≤ 28 * p) :
    chirpProductFixedBound a l w m ≤ (7056 * mtCvKf 125 + 200000) * p ^ 2 := by
  have hwA : w ≤ 125 * a := hw.trans (Nat.mul_le_mul_left 125 hpa)
  have hrX : 2 ^ l ≤ 84 * p := by omega
  have hfix := mt_cv_fix_le ha hl hwA hrX haUp
  have hprod : (84 * p) * a ≤ 7056 * p ^ 2 := by nlinarith only [haUp]
  have hfix' := hfix.trans (Nat.mul_le_mul_left (mtCvKf 125) hprod)
  have hheader := ring_header_length_le a (2 ^ l) w
  have hrw : 2 ^ l * w ≤ 3500 * p ^ 2 := by nlinarith only [Nat.mul_le_mul hr hw]
  have hmw : m * w ≤ 250 * p ^ 2 := by nlinarith only [Nat.mul_le_mul hm hw]
  have hp2 : p ≤ p ^ 2 := by nlinarith only [hp]
  have hsmall : 52 * (2 ^ l * w) + 18 * m * w + 37 * m + 12 * w + 27 * l +
      ldrHeaderCost a l w + 2 * (Spec.SignedRingProduct.header a (2 ^ l) w).length + 100 ≤ 200000 * p ^ 2 := by
    unfold ldrHeaderCost
    nlinarith only [hheader, hrw, hmw, hm, hw, hlUp, haUp, hr, hp, hp2]
  unfold chirpProductFixedBound
  calc
    _ ≤ mtCvKf 125 * (7056 * p ^ 2) + 200000 * p ^ 2 := by omega
    _ = _ := by ring

/-- The rest of line startup is quadratic only in precision and address width. -/
theorem chirp_line_fixed_quadratic {p W q l w m K : ℕ}
    (hp : 1 ≤ p) (hq : q ≤ 83 * p) (hl : l ≤ 10 * p)
    (hw : w ≤ 125 * p) (hm : m ≤ 2 * p)
    (hproduct : chirpProductFixedBound (q + 1) l w m ≤ K * p ^ 2) :
    chirpLineFixedBound W q l w m ≤
      32000 * (W + 1) ^ 2 + (K + 64000) * p ^ 2 := by
  have hp2 : p ≤ p ^ 2 := by nlinarith only [hp]
  have hW : W ≤ (W + 1) ^ 2 := by nlinarith
  have hW4 : (W + 4) ^ 2 ≤ 16 * (W + 1) ^ 2 := by nlinarith
  unfold chirpLineFixedBound IntegerMultBounds.MathlibTM2.Fast.TableVM.tblC
  nlinarith only [hp, hp2, hW, hW4, hq, hl, hw, hm, hproduct]

/-- Selected line startup has no hidden source-length or window-volume factor. -/
theorem chirp_selected_fixed_le (p α W : ℕ) (hp : 1 ≤ p) (hα : 1 ≤ α)
    (hαp : α ^ 2 ≤ p) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let q := chirpForwardPrecision p (chirpForwardGrowth p) l
    let w := q + l + chirpForwardGrowth p + 5
    chirpLineFixedBound W q l w m ≤
      32000 * (W + 1) ^ 2 + (7056 * mtCvKf 125 + 264000) * p ^ 2 := by
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let q := chirpForwardPrecision p (chirpForwardGrowth p) l
  let w := q + l + chirpForwardGrowth p + 5
  have hm1 : 1 ≤ m := Nat.mul_pos hα (Nat.succ_pos _)
  have hm : m ≤ 2 * p := chirpForwardWindow_le p α hαp
  have hr : 2 ^ l ≤ 28 * p :=
    (chirpRingSize_le m hm1).trans (by omega)
  have hl : l ≤ 10 * p := (chirpForwardRingLog_le p α hαp).trans (by omega)
  have hwidth := chirpForwardWidths_le p α hp hαp
  have hq : q ≤ 83 * p := hwidth.1
  have hw : w ≤ 125 * p := hwidth.2.1
  have hpq : p ≤ q + 1 := by dsimp [q, chirpForwardPrecision]; omega
  have hlq : l ≤ q + 1 := by dsimp [q, chirpForwardPrecision]; omega
  have hproduct := chirp_product_fixed_quadratic hp (by omega : 1 ≤ q + 1)
    (by omega : q + 1 ≤ 84 * p) hlq hl hw hpq hm hr
  have h := chirp_line_fixed_quadratic hp hq hl hw hm hproduct (W := W)
  have he (K : ℕ) : 7056 * K + 200000 + 64000 = 7056 * K + 264000 := by omega
  rw [he] at h
  exact h

end IntegerMultBounds.MathlibTM2.Cost
