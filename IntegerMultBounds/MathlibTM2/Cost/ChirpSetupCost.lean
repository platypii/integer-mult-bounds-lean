module

public import IntegerMultBounds.MathlibTM2.Cost.ChirpAddressCost

/-! # Numerical shared setup costs for the closed chirp group -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Loading a bank of arbitrary dimension has a linear, placement-independent cost. -/
theorem chirp_bank_load_cost {n T : ℕ} (rg : TblR n → Fin T) (input : Fin n → Fin T)
    (W e : ℕ) :
    chirpBankLoadCost rg input W e (fun _ => W) =
      (8 * n + 4) * W + 4 * e + 8 * n + 9 := by
  simp [chirpBankLoadCost, chirpBankCopiesCost, chirpBankInputAssignments,
    List.map_ofFn, Function.comp_def, List.ofFn_const]
  ring

/-- The five actual consumer banks instantiate the arbitrary-bank formula. -/
theorem chirp_consumer_banks_cost (W w : ℕ) :
    chirpBankFamilyCost LinePlacement.source W w LinePlacement.consumers =
      716 * W + 20 * w + 742 := by
  simp only [LinePlacement.consumers, ForwardBankPlacement.consumers, chirpForwardConsumers,
    List.map_cons, List.map_nil, LinePlacement.liftConsumer, chirpBankFamilyCost,
    chirp_bank_load_cost]
  ring

/-- Output controls cost only their final unary volume and nine binary scans. -/
theorem chirp_counters_cost (W p q l Γ w t : ℕ) (hpq : p ≤ q)
    (hw : q + l + Γ + 5 ≤ w) :
    LinePlacement.countersCost W p q l Γ w t =
      25 * tblC W w + 6 * (4 * w + t * (p + l + Γ + 5)) + 99 * W + 55 := by
  have hsum : l + 1 + (w - (l + 1)) + Γ + (w - Γ) + w + (q - p) +
      (p + l + Γ + 5) + (w - (q - p) - (p + l + Γ + 5)) = 4 * w := by omega
  simp [LinePlacement.countersCost, unaryCopiesCost, chirpOutputAssignments,
    chirpOutputDimensionValues]
  nlinarith only [hsum]

/-- Generating all G, K, E and normalization tables is linear in padded coefficient volume. -/
theorem chirp_tables_setup_le (W w q Γ m M S : ℕ) (hS : 1 ≤ S)
    (hM : M ≤ S) (hMm : M * m ≤ S) (hm : m ≤ S) :
    chirpTableScheduleCost W w q m M false + chirpTableScheduleCost W w q m M true +
      chirpOutputFactorSetupCost W w q Γ m ≤
        6000 * S * (q + 1) * tblC W w + 20 * S * w + 8 := by
  have hMq := Nat.mul_le_mul_right q hM
  have hMmq := Nat.mul_le_mul_right q hMm
  have hmq := Nat.mul_le_mul hm (Nat.sub_le q Γ)
  have hqS : q ≤ S * q := Nat.le_mul_of_pos_left _ hS
  have hcount :
      (M * ((3 * m + 1) * (310 * q + 122) + 150 * q + 445) + 12) +
      (M * (4 * m * (310 * q + 122) + 150 * q + 445) + 15) +
      (m * (310 * (q - Γ) + 113) + 150 * (q - Γ) + 445) + (4 * q + 13) ≤
        6000 * S * (q + 1) := by
    nlinarith only [hS, hM, hMm, hm, hMq, hMmq, hmq, hqS, Nat.sub_le q Γ]
  have hvol : M * (3 * m + 1) + 4 * (M * m) + m + 1 ≤ 10 * S := by
    nlinarith only [hM, hMm, hm, hS]
  have hcountC := Nat.mul_le_mul_right (tblC W w) hcount
  have hvolW := Nat.mul_le_mul_right w hvol
  simp only [chirpTableScheduleCost, chirpTableLength, Bool.false_eq_true,
    ↓reduceIte, chirpOutputFactorSetupCost]
  nlinarith only [hcountC, hvolW]

/-- Initialization is polynomial scalar work times the padded coefficient volume. -/
theorem chirp_initialize_cost_le (W b p q l Γ w t m M S : ℕ)
    (hS : 1 ≤ S) (hM : M ≤ S) (hMm : M * m ≤ S) (hm : m ≤ S)
    (ht : t ≤ S) (hb : b ≤ W) (hp : p ≤ q) (hq : q ≤ W)
    (hw1 : 1 ≤ w) (hw : q + l + Γ + 5 ≤ w) (hwW : w ≤ W) :
    LinePlacement.initializeCost W b p q l Γ w t m M ≤
      7000 * S * (W + 1) * (tblC W w + 1) := by
  have hsqrt : Nat.sqrt p ≤ W := (Nat.sqrt_le_self p).trans (hp.trans hq)
  have hl : l ≤ W := by omega
  have hsize : Nat.size (2 * w) ≤ 2 * W :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have htop : IntegerMultBounds.Schoenhage.Schedule.topN w ≤ 4 * W :=
    (IntegerMultBounds.Schoenhage.Schedule.topN_facts hw1).2.1.trans (by omega)
  have hH0 : tblC W 0 ≤ tblC W w := by unfold tblC; omega
  have hcoef : (((4 * (Nat.sqrt p + 1) + 7) + ((4 * l + 9) + 36)) + 5) ≤
      8 * W + 57 := by omega
  have hfirst := Nat.mul_le_mul hcoef hH0
  have hsizeC := Nat.mul_le_mul_right (tblC W w) hsize
  have hmul : chirpMultiplierSetupCost W w q w ≤
      (8 * W + 10) * tblC W w + 69 * W + 19 := by
    unfold chirpMultiplierSetupCost
    nlinarith only [hsizeC, hwW, hq, htop]
  have hwo : p + l + Γ + 5 ≤ W := by omega
  have htW := Nat.mul_le_mul ht hwo
  have hcounter := chirp_counters_cost W p q l Γ w t hp hw
  have hcounter' : LinePlacement.countersCost W p q l Γ w t ≤
      25 * tblC W w + 123 * W + 6 * (S * W) + 55 := by
    rw [hcounter]
    nlinarith only [hwW, htW]
  have htables := chirp_tables_setup_le W w q Γ m M S hS hM hMm hm
  have hqC := Nat.mul_le_mul_right (6000 * S * tblC W w) hq
  have hwS := Nat.mul_le_mul_left S hwW
  have hSW : W + 1 ≤ S * (W + 1) := Nat.le_mul_of_pos_left _ hS
  have hSWC := Nat.mul_le_mul_right (tblC W w) hSW
  unfold LinePlacement.initializeCost
  rw [chirp_consumer_banks_cost]
  nlinarith only [hfirst, hmul, hcounter', htables, hqC, hwS, hSW, hSWC, hb, hwW]

/-- The closed group's once-only setup and release have a uniform volume bound. -/
theorem chirp_selected_setup_le (s t α p : ℕ) (hp : 1 ≤ p) (hα : 1 ≤ α)
    (hαp : α ^ 2 ≤ p) (hst : s < t) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let Γ := chirpForwardGrowth p
    let q := chirpForwardPrecision p Γ l
    let w := q + l + Γ + 5
    let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
    LinePlacement.selectedGroupCost s t α p 0 ≤
      10000 * (t + m + 1) * (W + 1) * (tblC W w + 1) := by
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let B := chirpForwardCallerBase s t p
  let W := chirpForwardTableWord q B
  let M := chirpBlockCount t m
  let S := t + m + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hm1 : 1 ≤ m := Nat.mul_pos hα (Nat.succ_pos _)
  have hvol := chirpBlockCount_volume t m hm1
  have hM : M ≤ S := hvol.1.trans (by dsimp [S]; omega)
  have hMm : M * m ≤ S := (chirpBlockCount_mul_le t m).trans (by dsimp [S]; omega)
  have hm : m ≤ S := by dsimp [S]; omega
  have ht : t ≤ S := by dsimp [S]; omega
  have hs : s ≤ S := by omega
  have hB : 1 ≤ B := by dsimp [B, chirpForwardCallerBase]; omega
  have hwW : w ≤ W := (chirpForwardTableWord_good p Γ l B hB).2.2
  have hb : Nat.size B ≤ W := by dsimp [W, chirpForwardTableWord]; omega
  have hpq : p ≤ q := by dsimp [q, chirpForwardPrecision]; omega
  have hq : q ≤ W := by dsimp [W, chirpForwardTableWord]; omega
  have hw1 : 1 ≤ w := by dsimp [w]; omega
  have hwidth : q + l + Γ + 5 ≤ w := le_rfl
  have hinit := chirp_initialize_cost_le W (Nat.size B) p q l Γ w t m M S
    hS hM hMm hm ht hb hpq hq hw1 hwidth hwW
  have hcenter : chirpCenter s t m M ≤ S :=
    (chirpCenter_end_le hst.le (by omega) (fun j hj => chirpBlock_valid (by omega) hm1 hj)).trans (by dsimp [S]; omega)
  have hD := Nat.mul_le_mul hcenter hwW
  have hMH := Nat.mul_le_mul_right (tblC W w) hM
  have hMW := Nat.mul_le_mul_right W hM
  have hW : W + 1 ≤ S * (W + 1) := Nat.le_mul_of_pos_left _ hS
  have hWH := Nat.mul_le_mul_right (tblC W w) hW
  have hSL : S ≤ S * (W + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos W)
  have hSH := Nat.mul_le_mul_right (tblC W w) hSL
  have hH : tblC W w ≤ S * (W + 1) * tblC W w :=
    Nat.le_mul_of_pos_left _ (hS.trans hSL)
  have hcontrols : LinePlacement.controlsSetupCost W w s t m M ≤
      50 * S * (W + 1) * (tblC W w + 1) := by
    unfold LinePlacement.controlsSetupCost
    nlinarith only [hM, hD, hMH, hMW, hW, hWH, hSL, hSH, hH]
  have hrelease : LinePlacement.controlsReleaseCost s t m w M ≤ 20 * S * (W + 1) := by
    unfold LinePlacement.controlsReleaseCost
    nlinarith only [hM, hD, hW]
  have htop : IntegerMultBounds.Schoenhage.Schedule.topN w ≤ 4 * W :=
    (IntegerMultBounds.Schoenhage.Schedule.topN_facts hw1).2.1.trans (by omega)
  have htableVol : M * (7 * m + 1) + m + 1 ≤ 10 * S := by
    nlinarith only [hM, hMm, hm, hS]
  have htableW := Nat.mul_le_mul htableVol hwW
  have hwo : p + l + Γ + 5 ≤ W := by omega
  have htW := Nat.mul_le_mul ht hwo
  have hretained : LinePlacement.retainedReleaseCost p q l Γ w t m M ≤
      120 * S * (W + 1) := by
    unfold LinePlacement.retainedReleaseCost
    nlinarith only [hwW, hq, htop, htableW, htW, hW]
  have hsw := Nat.mul_le_mul hs hwW
  unfold LinePlacement.selectedGroupCost LinePlacement.groupRunBound
  simp only [Nat.zero_mul, Nat.zero_add]
  change ((LinePlacement.initializeCost W (Nat.size B) p q l Γ w t m M +
      (2 * tblC W w + (6 * (s * w) + 11 * W + 7)) +
      (LinePlacement.controlsSetupCost W w s t m M + 8)) +
    (LinePlacement.controlsReleaseCost s t m w M +
      ((2 * (s * w) + 2) + (LinePlacement.retainedReleaseCost p q l Γ w t m M +
        (218 * W + 12 * w + 243))))) ≤ 10000 * S * (W + 1) * (tblC W w + 1)
  nlinarith only [hinit, hcontrols, hrelease, hretained, hsw, hwW, hW, hWH]

/-- Shared setup is at most cubic in the address width, times the coefficient volume. -/
theorem chirp_selected_setup_cubic (s t α p : ℕ) (hp : 1 ≤ p) (hα : 1 ≤ α)
    (hαp : α ^ 2 ≤ p) (hst : s < t) :
    let m := chirpForwardWindow p α
    let l := chirpForwardRingLog p α
    let q := chirpForwardPrecision p (chirpForwardGrowth p) l
    let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
    LinePlacement.selectedGroupCost s t α p 0 ≤ 6000000 * (t + m + 1) * (W + 1) ^ 3 := by
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  let w := q + l + Γ + 5
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  have hB : 1 ≤ chirpForwardCallerBase s t p := by unfold chirpForwardCallerBase; omega
  have hw : w ≤ W := (chirpForwardTableWord_good p Γ l _ hB).2.2
  have htable : tblC W w + 1 ≤ 600 * (W + 1) ^ 2 := by
    unfold tblC
    nlinarith only [hw, Nat.zero_le (W ^ 2)]
  calc
    _ ≤ 10000 * (t + m + 1) * (W + 1) * (tblC W w + 1) :=
      chirp_selected_setup_le s t α p hp hα hαp hst
    _ ≤ 10000 * (t + m + 1) * (W + 1) * (600 * (W + 1) ^ 2) :=
      Nat.mul_le_mul_left _ htable
    _ = _ := by ring


/-- Unconditional setup-plus-work comparison for every admissible group size. -/
theorem chirp_selected_total_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p α s t N : ℕ) [NeZero s] [NeZero t],
      1 ≤ p → 1 ≤ α → α ^ 2 ≤ p → s < t →
      let m := chirpForwardWindow p α
      let l := chirpForwardRingLog p α
      let q := chirpForwardPrecision p (chirpForwardGrowth p) l
      let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
      (LinePlacement.selectedGroupCost s t α p N : ℝ) ≤
        6000000 * ((t + m + 1 : ℕ) : ℝ) * ((W + 1 : ℕ) : ℝ) ^ 3 +
          C * (N : ℝ) * ((p ^ 2 + t : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨C, hC, hgroup⟩ := chirp_selected_group_le
  refine ⟨C, hC, ?_⟩
  intro p α s t N _ _ hp hα hαp hst
  dsimp only
  have hsetup := chirp_selected_setup_cubic s t α p hp hα hαp hst
  have hsetup' : (LinePlacement.selectedGroupCost s t α p 0 : ℝ) ≤
      6000000 * ((t + chirpForwardWindow p α + 1 : ℕ) : ℝ) *
        ((chirpForwardTableWord (chirpForwardPrecision p (chirpForwardGrowth p)
          (chirpForwardRingLog p α)) (chirpForwardCallerBase s t p) + 1 : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast hsetup
  exact (hgroup p α s t N hp hα hαp hst).trans (add_le_add hsetup' le_rfl)

/-- A dimension-sized group amortizes all executed setup, with no supplied cost inequality. -/
theorem chirp_selected_amortized_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p α s t N : ℕ) [NeZero s] [NeZero t],
      1 ≤ p → 1 ≤ α → α ^ 2 ≤ p → s < t → p ^ 2 ≤ t →
      let l := chirpForwardRingLog p α
      let q := chirpForwardPrecision p (chirpForwardGrowth p) l
      let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
      (W + 1) ^ 3 ≤ N →
      (LinePlacement.selectedGroupCost s t α p N : ℝ) ≤
        C * (N : ℝ) * (t : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨C, hC, hgroup⟩ := chirp_selected_long_group_le
  refine ⟨C + 24000000, by positivity, ?_⟩
  intro p α s t N _ _ hp hα hαp hst ht
  dsimp only
  intro hN
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let q := chirpForwardPrecision p (chirpForwardGrowth p) l
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  have hm : m ≤ 2 * p := chirpForwardWindow_le p α hαp
  have hp2 : p ≤ p ^ 2 := by nlinarith only [hp]
  have hS : t + m + 1 ≤ 4 * t := by omega
  have hscale := Nat.mul_le_mul hS hN
  have hsetup : LinePlacement.selectedGroupCost s t α p 0 ≤ 24000000 * N * t := by
    calc
      _ ≤ 6000000 * (t + m + 1) * (W + 1) ^ 3 :=
        chirp_selected_setup_cubic s t α p hp hα hαp hst
      _ = 6000000 * ((t + m + 1) * (W + 1) ^ 3) := by ring
      _ ≤ 6000000 * ((4 * t) * N) := Nat.mul_le_mul_left _ hscale
      _ = _ := by ring
  have hsetup' : (LinePlacement.selectedGroupCost s t α p 0 : ℝ) ≤
      24000000 * (N : ℝ) * t := by exact_mod_cast hsetup
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hPow : (1 : ℝ) ≤ (p : ℝ) ^ (129 / 128 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hsetupPow := hsetup'.trans (le_mul_of_one_le_right (by positivity) hPow)
  calc
    _ ≤ (LinePlacement.selectedGroupCost s t α p 0 : ℝ) +
        C * (N : ℝ) * t * (p : ℝ) ^ (129 / 128 : ℝ) := hgroup p α s t N hp hα hαp hst ht
    _ ≤ (24000000 * (N : ℝ) * t) * (p : ℝ) ^ (129 / 128 : ℝ) +
        C * (N : ℝ) * t * (p : ℝ) ^ (129 / 128 : ℝ) := add_le_add hsetupPow le_rfl
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
