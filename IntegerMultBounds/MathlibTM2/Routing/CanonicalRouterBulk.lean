module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterBits

/-! The actual canonical residue inputs discharge the repeated scheduler's
stage-data premises. All residues use the same original-matching program. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactDigits IntegerMultBounds.MathlibTM2.Layer.CompactGadget
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section


def canonicalRouterDelimiter {K : ℕ} : Fin (prime + K + 4) :=
  ⟨8, by
    have h := IntegerMultBounds.Networks.two_pow_le_coefficientBound
      (a := 3) (by
        rw [IntegerMultBounds.Networks.coefficientExponent_eq]
        have hpow := Nat.pow_le_pow_right (n := 2) (by decide : 0 < 2) (by decide : 2 ≤ 2 ^ 16)
        exact (by decide : 3 ≤ 2 ^ 2).trans hpow)
    have hp := IntegerMultBounds.Networks.Shared50ModularControl.coefficientBound_lt_prime
    omega⟩

variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3) (reverse : Bool)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = R * 2 ^ n)
    (hlen : ∀ row ∈ l, row.length = B ∧ ∀ x ∈ row, x.val < 8)

local notation "input" => canonicalRouterInput n hn R B hR hB mate hinv k reverse hQ hA l hl hlen

/-- Full residue frame budget from dimensions and scalar widths. -/
def canonicalRouterFrameWidth (r : Fin (canonicalRouterStride n)) : ℕ :=
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let a := canonicalRouterArithmetic n r R B hR hB
  let L := a.w.indexBits + a.w.strideBits
  originalMatchingScheduleT 6 *
    ((canonicalRouterMetadataWidth n r R B hR hB + canonicalRouterCountWidth n r +
      p.wy * (2 * L + 2) + a.w.strideBits + a.w.strideBits) +
      (n * (2 * L + 2) + 12 * L + 12) + 1)

/-- One polynomial frame budget for every residue. -/
def canonicalRouterUniformFrameWidth (n R B : ℕ) : ℕ :=
  let D := Nat.clog 2 (4 * n + 2) + 1
  originalMatchingScheduleT 6 *
    (canonicalRouterUniformMetadataWidth n R B + canonicalScalarWidth (n * (4 * D + 2)) +
      2 * n * (4 * D + 2) + 26 * D + 13)

include hn in
theorem canonicalRouterFrameWidth_uniform (r : Fin (canonicalRouterStride n)) :
    canonicalRouterFrameWidth n R B hR hB r ≤ canonicalRouterUniformFrameWidth n R B := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  let a := canonicalRouterArithmetic n r R B hR hB
  let D := Nat.clog 2 (4 * n + 2) + 1
  have hm := canonicalRouterMetadataWidth_uniform n hn r R B hR hB
  change canonicalRouterMetadataWidth n r R B hR hB ≤ _ at hm
  have hcount := canonicalRouterCountWidth_le n hn r
  obtain ⟨hi, hs, _, _, _, _⟩ := canonicalRouterDescriptorWidths_le n hn r
  have haw : a.w = canonicalStageWidths p := rfl
  have hL : a.w.indexBits + a.w.strideBits ≤ 2 * D := by
    rw [haw]
    dsimp only [p, D]
    omega
  have hstride : a.w.strideBits ≤ D := by simpa only [haw, p, D] using hs
  have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
  have hwy : p.wy ≤ n := by omega
  have hc : 2 * (a.w.indexBits + a.w.strideBits) + 2 ≤ 4 * D + 2 := by omega
  have hp := Nat.mul_le_mul hwy hc
  have hnp := Nat.mul_le_mul_left n hc
  unfold canonicalRouterFrameWidth canonicalRouterUniformFrameWidth
  apply Nat.mul_le_mul_left
  have he : 2 * n * (4 * D + 2) = n * (4 * D + 2) + n * (4 * D + 2) := by ring
  dsimp only [D] at he
  rw [he]
  dsimp only [p, a, D] at *
  omega

include hn in
theorem canonicalRouterFrameWidths_sum_le (stages : List (Fin (canonicalRouterStride n))) :
    (stages.map (canonicalRouterFrameWidth n R B hR hB)).sum ≤
      stages.length * canonicalRouterUniformFrameWidth n R B := by
  induction stages with
  | nil => simp
  | cons r stages ih =>
    have hr := canonicalRouterFrameWidth_uniform n hn R B hR hB r
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Actual canonical profile production has one polynomial budget for every residue. -/
theorem canonicalRouterProfileProductionCost_le (r : Fin (canonicalRouterStride n)) :
    matchingFullProfileProductionCost (input r).p
      ((input r).w.indexBits + (input r).w.strideBits) (input r).w.strideBits
      (canonicalRouterCountWidth n r) ≤
      matchingFullProfileProductionBound n (2 * (Nat.clog 2 (4 * n + 2) + 1))
        (Nat.clog 2 (4 * n + 2) + 1)
        (canonicalScalarWidth (n * (4 * (Nat.clog 2 (4 * n + 2) + 1) + 2))) := by
  let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
  have ht : 3 * p.wc + p.wy = n := routerProfileParameters_total n _ _ hn r
  have hd : p.n ≤ n := routerDigits_le_width n _ _
  have hp : p.n * p.K ≤ n := by unfold Par.wy at ht; omega
  obtain ⟨hi, hs, _, _, _, _⟩ := canonicalRouterDescriptorWidths_le n hn r
  have hc := canonicalRouterCountWidth_le n hn r
  dsimp only [canonicalRouterInput, canonicalGeneratedInput]
  apply matchingFullProfileProductionCost_le_bound _ _ _ _ _ _ _ _ hd hp ?_ hs hc
  dsimp only [canonicalRouterArithmetic, canonicalStageArithmetic]
  omega

/-- Original-to-local matching-table conversion has a residue-independent runtime bound. -/
theorem canonicalRouterTableConversionCost_le (r : Fin (canonicalRouterStride n)) :
    reservoirClassLocalTableCost n (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      ((input r).w.indexBits + (input r).w.strideBits) ≤
      reservoirClassLocalTableCost n 0 (2 * (Nat.clog 2 (4 * n + 2) + 1)) := by
  apply reservoirClassLocalTableCost_le
  dsimp only [canonicalRouterInput, canonicalGeneratedInput, canonicalRouterArithmetic, canonicalStageArithmetic]
  obtain ⟨hi, hs, _, _, _, _⟩ := canonicalRouterDescriptorWidths_le n hn r
  omega

/-- Matching setup and its coordinate cleanup are polynomial overhead around repair. -/
theorem canonicalRouterMatchingPrice_le (r : Fin (canonicalRouterStride n)) :
    matchingPlacedRepairPrice (input r) (canonicalRouterCountWidth n r) ≤
      (input r).price +
      (matchingFullProfileProductionBound n (2 * (Nat.clog 2 (4 * n + 2) + 1))
        (Nat.clog 2 (4 * n + 2) + 1)
        (canonicalScalarWidth (n * (4 * (Nat.clog 2 (4 * n + 2) + 1) + 2))) +
        2 * canonicalRouterUniformMetadataWidth n R B + 2 : ℕ) := by
  have hp := canonicalRouterProfileProductionCost_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
  have hc := canonicalRouterInput_length_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
    (input r).coordinateRegister (input r).coordinateRegister_ne_stream
  rw [(input r).coordinateWord] at hc
  have hm := canonicalRouterMetadataWidth_uniform n hn r R B hR hB
  change canonicalRouterMetadataWidth n r R B hR hB ≤ _ at hm
  have hcleanup : (2 * (input r).coordinateWords.length + 2 : ℕ) ≤
      2 * canonicalRouterUniformMetadataWidth n R B + 2 := by omega
  have hp' : (matchingFullProfileProductionCost (input r).p
      ((input r).w.indexBits + (input r).w.strideBits) (input r).w.strideBits
      (canonicalRouterCountWidth n r) : ℝ) ≤
      (matchingFullProfileProductionBound n (2 * (Nat.clog 2 (4 * n + 2) + 1))
        (Nat.clog 2 (4 * n + 2) + 1)
        (canonicalScalarWidth (n * (4 * (Nat.clog 2 (4 * n + 2) + 1) + 2))) : ℕ) := by exact_mod_cast hp
  have hc' : ((2 * (input r).coordinateWords.length + 2 : ℕ) : ℝ) ≤
      (2 * canonicalRouterUniformMetadataWidth n R B + 2 : ℕ) := by exact_mod_cast hcleanup
  unfold matchingPlacedRepairPrice
  push_cast at hc' ⊢
  linarith

/-- All original-matching setup and erasure, excluding the repair execution itself. -/
def canonicalRouterOriginalSetupBudget (n R B : ℕ) : ℕ :=
  let D := Nat.clog 2 (4 * n + 2) + 1
  reservoirClassLocalTableCost n 0 (2 * D) +
    (matchingFullProfileProductionBound n (2 * D) D (canonicalScalarWidth (n * (4 * D + 2))) +
      2 * canonicalRouterUniformMetadataWidth n R B + 2) +
    (2 * (n * (4 * D + 2)) + 2)

theorem canonicalRouterOriginalPrice_le (r : Fin (canonicalRouterStride n)) :
    originalMatchingPlacedPrice (input r) (canonicalRouterCountWidth n r) n
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) ≤
      (input r).price + (canonicalRouterOriginalSetupBudget n R B : ℕ) := by
  let D := Nat.clog 2 (4 * n + 2) + 1
  let borrowed := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
  have hm := canonicalRouterMatchingPrice_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
  have ht := canonicalRouterTableConversionCost_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
  have hL : (input r).w.indexBits + (input r).w.strideBits ≤ 2 * D := by
    dsimp only [canonicalRouterInput, canonicalGeneratedInput, canonicalRouterArithmetic, canonicalStageArithmetic]
    obtain ⟨hi, hs, _, _, _, _⟩ := canonicalRouterDescriptorWidths_le n hn r
    dsimp only [D]
    omega
  have hc := Nat.mul_le_mul (Nat.sub_le n (3 * borrowed))
    (show 2 * ((input r).w.indexBits + (input r).w.strideBits) + 2 ≤ 4 * D + 2 by omega)
  have hcleanup : (2 * ((n - 3 * borrowed) *
      (2 * ((input r).w.indexBits + (input r).w.strideBits) + 2)) + 2 : ℕ) ≤
      2 * (n * (4 * D + 2)) + 2 := by omega
  have htR : (reservoirClassLocalTableCost n borrowed ((input r).w.indexBits + (input r).w.strideBits) : ℝ) ≤
      (reservoirClassLocalTableCost n 0 (2 * D) : ℕ) := by exact_mod_cast ht
  have hcR : ((2 * ((n - 3 * borrowed) *
      (2 * ((input r).w.indexBits + (input r).w.strideBits) + 2)) + 2 : ℕ) : ℝ) ≤
      (2 * (n * (4 * D + 2)) + 2 : ℕ) := by exact_mod_cast hcleanup
  unfold originalMatchingPlacedPrice canonicalRouterOriginalSetupBudget
  dsimp only [D, borrowed] at htR hcR
  push_cast at hm htR hcR ⊢
  linarith

theorem canonicalRouterFrame_length_le (r : Fin (canonicalRouterStride n)) :
    (originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
      k mate canonicalRouterDelimiter).length ≤ canonicalRouterFrameWidth n R B hR hB r := by
  have hf := originalMatchingFrame_length_le (input r) (canonicalRouterCountWidth n r) n
    (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
    k mate canonicalRouterDelimiter (canonicalRouterMetadataWidth n r R B hR hB)
    (fun j hj => canonicalRouterInput_length_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r j hj)
  simpa only [canonicalRouterFrameWidth, canonicalRouterInput, canonicalGeneratedInput] using hf

/-- Complete setup overhead for one framed canonical residue. -/
def canonicalRouterStageSetupBudget (n R B : ℕ) : ℕ :=
  canonicalRouterOriginalSetupBudget n R B +
    (6 * canonicalRouterUniformFrameWidth n R B + 2 * originalMatchingScheduleT 6 + 2)

theorem canonicalRouterStepPrice_le (r : Fin (canonicalRouterStride n)) :
    originalMatchingStepPrice (input r) (canonicalRouterCountWidth n r) n
      (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
      k mate canonicalRouterDelimiter ≤
      (input r).price + (canonicalRouterStageSetupBudget n R B : ℕ) := by
  have hf := (canonicalRouterFrame_length_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r).trans
    (canonicalRouterFrameWidth_uniform n hn R B hR hB r)
  have hs := originalMatchingStepPrice_le (input r) (canonicalRouterCountWidth n r) n
    (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
    k mate canonicalRouterDelimiter (canonicalRouterUniformFrameWidth n R B) hf
  have hp := canonicalRouterOriginalPrice_le n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r
  unfold canonicalRouterStageSetupBudget
  push_cast at hs hp ⊢
  linarith


/-- Execute a concrete list of bulk residues. All stage data, program identities
and metadata admissibility are discharged by the canonical input construction. -/
theorem canonicalRouterBulk_exec (stages : List (Fin (canonicalRouterStride n)))
    (v : HS (originalMatchingScheduleT 6 + 3) Q (prime + K) Unit)
    (S : Stacks (originalMatchingScheduleT 6 + 3) (prime + K))
    (ready : FramedCoreReady (originalMatchingScheduleStream 6) (R * 2 ^ n) B S)
    (hinput : S.R (framedCoreAux (originalMatchingScheduleT 6) 0) = delimitedScheduleInput
      (fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
        (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
        (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
        (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
        k mate canonicalRouterDelimiter) stages)
    (hsaved : S.R (framedCoreAux (originalMatchingScheduleT 6) 2) = []) :
    let r₀ : Fin (canonicalRouterStride n) := ⟨0, by
      have := canonicalRouterGap_pos n
      unfold canonicalRouterStride
      omega⟩
    let program : Pr Empty (originalMatchingScheduleT 6) Q (prime + K) Unit :=
      originalMatchingPlacedProgram (input r₀)
        (originalMatchingProducerEmbed (inactiveClassifierPlacementT 6))
        (originalMatchingRepairEmbed (inactiveClassifierPlacementT 6)) Empty.elim Empty.elim k reverse
    ∃ (v' : HS (originalMatchingScheduleT 6 + 3) Q (prime + K) Unit) (steps : ℕ),
      v'.user = v.user ∧
      (steps : ℝ) ≤ delimitedSchedulePrice
        (fun r => originalMatchingStepPrice (input r) (canonicalRouterCountWidth n r) n
          (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
          (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
          (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter) stages +
        (2 * (delimitedScheduleInput (fun r => originalMatchingFrame (input r) (canonicalRouterCountWidth n r) n
          (routingReservoirWidth n (canonicalRouterGap n)) (routingReservoir_fit n (canonicalRouterGap n) hn)
          (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
          (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k mate canonicalRouterDelimiter) stages).length + 3 : ℕ) ∧
      Exec (Empty.elim : Empty → Pr Empty (originalMatchingScheduleT 6 + 3) Q (prime + K) Unit)
        (delimitedScheduleProgram (framedCoreAux (originalMatchingScheduleT 6) 0)
          (framedCoreAux (originalMatchingScheduleT 6) 2)
          (framedCoreCallProgram (originalMatchingScheduleStream 6) canonicalRouterDelimiter
            (fun x => decide (x.val < 8)) Empty.elim program)) (mk v S) steps
        (mk v' { S with R := Function.update S.R (framedCoreEmbed (originalMatchingScheduleT 6) (originalMatchingScheduleStream 6)) (repairStreamEffect (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) B (S.R (framedCoreEmbed (originalMatchingScheduleT 6) (originalMatchingScheduleStream 6)))) }) := by
  dsimp only
  obtain ⟨rows, hrows, hshape, hstream⟩ := ready.stream
  have heffect : delimitedScheduleEffect
      (fun r => repairStreamEffect (canonicalRouterStagePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r) B)
      stages (S.R (framedCoreEmbed (originalMatchingScheduleT 6) (originalMatchingScheduleStream 6))) = repairStreamEffect (canonicalRouterSchedulePerm n hn R B hR hB mate hinv k reverse hQ hA l hl hlen stages) B (S.R (framedCoreEmbed (originalMatchingScheduleT 6) (originalMatchingScheduleStream 6))) := by
    rw [hstream]
    rw [repairStreamEffects_moveRecs _ stages rows hrows (fun row hr => (hshape row hr).1)]
    exact flatten_moveRecs _ rows (fun row hr => (hshape row hr).1)
  rw [← heffect]
  apply framedOriginalMatchingSchedule_exec (inputs := input) (Lc := canonicalRouterCountWidth n)
    (ι₀ := Empty.elim) (coreBody := Empty.elim) (ι := Empty.elim) (body := Empty.elim)
    (hbody := fun f => f.elim) (ιouter := Empty.elim) (outerBody := Empty.elim)
    (houter := fun f => f.elim) (program := _)
    (n := n) (H := routingReservoirWidth n (canonicalRouterGap n))
    (hfit := routingReservoir_fit n (canonicalRouterGap n) hn)
    (w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (hw := routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n))
    (k := k) (mate := mate) (hinv := hinv) (reverse := reverse)
    (delimiter := canonicalRouterDelimiter) (scan := fun x => decide (x.val < 8)) (stages := stages)
    (hstop := by rfl) (hcore := fun _ _ f => f.elim)
    (hcode := ?_) (data := canonicalRouterStage_data n hn R B hR hB mate hinv k reverse hQ hA l hl hlen)
    (hword := ?_) (v := v) (S := S) ready hinput hsaved
  · intro r hr
    exact canonicalRouterStage_program n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r _
  · intro r hr j hj x hx
    exact decide_eq_true (canonicalRouterStage_words n hn R B hR hB mate hinv k reverse hQ hA l hl hlen r j x hx)

end
end IntegerMultBounds.MathlibTM2.Routing
