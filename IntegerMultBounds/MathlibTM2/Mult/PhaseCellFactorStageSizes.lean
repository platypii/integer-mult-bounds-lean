module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorIntegerMatrix
public import IntegerMultBounds.MathlibTM2.Fast.BandFits
public import IntegerMultBounds.NLogN.SchurSizes

/-! Bound the actual computed boundary factor stages using their proved rank-matrix invariant. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes

variable {s : ℕ} [NeZero s]

theorem factorIntegerStage_sizes (A q w K : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) (p : ℕ) (hp : 2 ≤ p) (hP : 2 ≤ q)
    (hinv : StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card) (1 / (8 * (2 * (p : ℝ))))
      (9 / 4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1 / (8 * (2 * (p : ℝ))) / 2)
    (hηβ : 5 * (1 / 2 ^ q : ℝ) ≤ 2 * (β / 4) / 9)
    (hK : (1 - β / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * (1 / 2 ^ q : ℝ)) / (β / 4))
    (hsmall : 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (B.card : ℝ) ^ 2 * ((1 / 2 ^ q : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (m : ℕ) (hm : m < B.card) :
    (β ≤ gv q (stgZ q K (factorRankIntegerMatrix B W columns) m m m) ∧ gv q (stgZ q K (factorRankIntegerMatrix B W columns) m m m) ≤ 3) ∧
      ∀ i l, m ≤ i → m ≤ l → |gv q (stgZ q K (factorRankIntegerMatrix B W columns) m i l)| ≤ 3 := by
  set η : ℝ := 1 / 2 ^ q
  have hη : 0 ≤ η := by positivity
  set η' := η * (1 + 60 * 3 / β ^ 2) with hη'
  have hle : η ≤ η' := by
    have : 0 ≤ η * (60 * 3 / β ^ 2) := by positivity
    nlinarith
  have hrd' : ∀ x, |rdP q x - x| ≤ η' := fun x => (rdP_err q x).trans (by simpa [η] using hle)
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (2 : ℝ) ≤ 2 * (p : ℝ) := by linarith
  have hs1 : (1 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 1 ≤ B.card)
  have hμ : (0 : ℝ) < 1 / (8 * (2 * (p : ℝ))) := by positivity
  obtain ⟨-, hmu', -, -, -⟩ := bandM_arith (2 * (p : ℝ)) (B.card : ℝ) η' hqR hs1 (by positivity) hsmall
  have hm'' : 9 / 4 + (B.card : ℝ) * (η' * (B.card + 3)) ≤ 3 := by
    have hη0 : 0 ≤ η' := by positivity
    have hss : (B.card : ℝ) ≤ (B.card : ℝ) ^ 2 := by nlinarith
    have h1 : (B.card : ℝ) * (η' * (B.card + 3)) ≤ 4 * ((B.card : ℝ) ^ 2 * η') := by
      have e : (B.card : ℝ) * (η' * (B.card + 3)) = (B.card : ℝ) ^ 2 * η' + 3 * ((B.card : ℝ) * η') := by ring
      have := mul_le_mul_of_nonneg_right hss hη0
      rw [e]; linarith
    have hq4 : (1 : ℝ) ≤ (2 * (p : ℝ)) ^ 2 := by nlinarith
    have h3 : 2 ^ 16 * ((B.card : ℝ) ^ 2 * η') ≤ 1 := by
      calc 2 ^ 16 * ((B.card : ℝ) ^ 2 * η') = 1 * (2 ^ 16 * ((B.card : ℝ) ^ 2 * η')) := (one_mul _).symm
        _ ≤ (2 * (p : ℝ)) ^ 2 * (2 ^ 16 * ((B.card : ℝ) ^ 2 * η')) :=
          mul_le_mul_of_nonneg_right hq4 (by positivity)
        _ = 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (B.card : ℝ) ^ 2 * η' := by ring
        _ ≤ 1 := hsmall
    linarith
  have hmul : ∀ a c, |a| ≤ 3 → 1 / (8 * (2 * (p : ℝ))) / 2 ≤ c → c ≤ 3 →
      |PhaseCellMatrix.machMul (rdP q) K a c - a / c| ≤ η' := by
    intro a c ha hc hc3
    have e : PhaseCellMatrix.machMul (rdP q) K a c = NewtonRecip.recipMul (rdP q) 3 β K a c := by
      simp only [PhaseCellMatrix.machMul, NewtonRecip.recipMul, hβp.trans hc, hc3, ha, and_self,
        ite_true]
    rw [e]
    exact NewtonRecip.recipMul_err (rdP q) η (rdP_err q) 3 β (by norm_num) hβ hηβ K hK a c
  have hZvalue := factorRankIntegerMatrix_value A q w B W columns hlen hformat hA hw
  have hInv : StageInv (gvM q (factorRankIntegerMatrix B W columns)) (Finset.range B.card)
      (1 / (8 * (2 * (p : ℝ)))) (9 / 4) := by rw [hZvalue]; exact hinv
  have hcard : ((B.card : ℕ) : ℝ) ≤ (B.card : ℝ) := le_rfl
  obtain ⟨hpiv, hent⟩ := stg_sizes (rdP q) (mRule q K) η' hrd' _ 3 B.card hμ (by norm_num) hmul
    (gvM q (factorRankIntegerMatrix B W columns)) 0 B.card (9 / 4) hcard (by simpa using hInv)
    (by have := hm''; nlinarith) (by linarith) m hm
  have hmap : ∀ i l, gv q (stgZ q K (factorRankIntegerMatrix B W columns) m i l) =
      stg (rdP q) (mRule q K) (gvM q (factorRankIntegerMatrix B W columns)) 0 m i l := fun i l => by
    rw [← stgZ_map q K hP]; rfl
  simp only [zero_add] at hpiv hent
  refine ⟨⟨?_, ?_⟩, fun i l hi hl => ?_⟩
  · rw [hmap]; linarith [hpiv.1]
  · rw [hmap]; exact hpiv.2
  · by_cases his : i < B.card ∧ l < B.card
    · rw [hmap]; exact hent i l hi his.1 hl his.2
    · rw [stgZ_out q K B.card _ (factorRankIntegerMatrix_out B W columns) m i l
        (by omega), gv_zero]
      norm_num

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
