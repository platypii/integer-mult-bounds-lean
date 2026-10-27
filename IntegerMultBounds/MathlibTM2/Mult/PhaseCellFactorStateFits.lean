module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorStageSizes

/-! Every record in the actual computed boundary window factorization fits its allocated width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.MathlibTM2.Mult.Sizes
  IntegerMultBounds.MathlibTM2.Mult.BandList

variable {s : ℕ} [NeZero s]

theorem factorIntegerState_fits (A q w K : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) (p : ℕ) (hp : 2 ≤ p) (hP : 2 ≤ q)
    (hinv : StageInv (factorRankMatrix A q w B W columns) (Finset.range B.card) (1 / (8 * (2 * (p : ℝ))))
      (9 / 4))
    (β : ℝ) (hβ : 0 < β) (hβp : β ≤ 1 / (8 * (2 * (p : ℝ))) / 2)
    (hηβ : 5 * (1 / 2 ^ q : ℝ) ≤ 2 * (β / 4) / 9)
    (hK : (1 - β / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * (1 / 2 ^ q : ℝ)) / (β / 4))
    (hsmall : 2 ^ 16 * (2 * (p : ℝ)) ^ 2 * (B.card : ℝ) ^ 2 * ((1 / 2 ^ q : ℝ) * (1 + 60 * 3 / β ^ 2)) ≤ 1)
    (hwidth : (6 / β + 1) * 2 ^ q < (2 : ℝ) ^ (w - 1)) (m : ℕ) (hm : m < B.card) :
    FacFits w q K (facState q K (factorIntegerRows (factorWindowValues B W columns)) (factorIntegerRows (factorInputValues B W B.card columns)) m) := by
  obtain ⟨hpiv, hent⟩ := factorIntegerStage_sizes A q w K B W columns hlen hformat hA hw p hp hP hinv β hβ hβp hηβ hK hsmall m hm
  set Z := stgZ q K (factorRankIntegerMatrix B W columns) m with hZ
  set C : ℝ := 6 / β + 1
  have hβ1 : β ≤ 1 := hβp.trans (by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    rw [div_div, div_le_one (by positivity)]; nlinarith)
  have h3C : (3 : ℝ) ≤ C := by
    have : 6 ≤ 6 / β := by rw [le_div_iff₀ hβ]; linarith
    simp only [C]; linarith
  have h2C : 2 / β ≤ C := by
    have : 0 ≤ 4 / β := by positivity
    have e : 6 / β = 2 / β + 4 / β := by ring
    simp only [C]; linarith
  have hη1 : (1 / 2 ^ q : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  set c := Z m m
  have hc0 : 0 < gv q c := lt_of_lt_of_le hβ hpiv.1
  have hnew : ∀ n, 0 ≤ gv q c * gv q (newtonZ q c n) ∧ gv q c * gv q (newtonZ q c n) ≤ 2 ∧
      |gv q (newtonZ q c n)| ≤ 2 / β := by
    intro n
    have h := NewtonRecip.newtonR_range (rdP q) _ (rdP_err q) β (gv q c) hβ hpiv.1 hpiv.2 hηβ n
    rw [newtonZ_eq q hP c n] at h
    have hr0 : 0 ≤ gv q (newtonZ q c n) := by
      by_contra hneg; have := not_le.mp hneg; nlinarith
    have hβr : β * gv q (newtonZ q c n) ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_right hpiv.1 hr0) h.2
    refine ⟨h.1, h.2, ?_⟩
    rw [abs_of_nonneg hr0, le_div_iff₀ hβ]; linarith
  have hrd : ∀ a r : ℤ, |gv q ((a * r).tdiv (2 ^ q))| ≤ |gv q a * gv q r| + 1 := by
    intro a r
    have e := rdP_mul_grid q a r
    have h := rdP_err q (gv q a * gv q r)
    simp only [gv] at e h ⊢
    rw [← e]
    have := abs_sub_abs_le_abs_sub (rdP q ((a : ℝ) / 2 ^ q * ((r : ℝ) / 2 ^ q)))
      ((a : ℝ) / 2 ^ q * ((r : ℝ) / 2 ^ q))
    linarith
  have hfit : ∀ z : ℤ, |gv q z| ≤ C → Fits w (⟨z, 0⟩ : GaussianInt) := fun z hz => fits_of_gv hz hwidth
  rw [factorIntegerState_window A q w K B W columns hlen hformat hA hw hP m hm.le,
    List.range'_succ,List.map_cons]
  simp only [winRowZ, ← hZ]
  rw [List.range'_succ, List.map_cons]
  refine ⟨hfit _ ((hent m m le_rfl le_rfl).trans h3C), fun n _ => ⟨hfit _ ((hnew n).2.2.trans h2C),
    hfit _ ?_⟩, hfit _ ((hnew K).2.2.trans h2C), fun a ha => ?_, fun row hrow => ?_⟩
  · refine (hrd _ _).trans ?_
    rw [abs_of_nonneg (hnew n).1]; linarith [(hnew n).2.1]
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    exact hfit _ ((hent m l le_rfl (by have := List.mem_range'_1.mp hl; omega)).trans h3C)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hrow
    have hi' := List.mem_range'_1.mp hi
    have hh : (winRowZ W Z m i).headD 0 = Z i m := by
      rw [winRowZ, List.range'_succ, List.map_cons, List.headD_cons]
    simp only [facMul, hh]
    refine ⟨hfit _ ((hent i m (by omega) le_rfl).trans h3C), hfit _ ?_⟩
    refine (hrd _ _).trans ?_
    rw [abs_mul]
    have h1 := hent i m (by omega) le_rfl
    have h2 := (hnew K).2.2
    have : |gv q (Z i m)| * |gv q (newtonZ q c K)| ≤ 3 * (2 / β) :=
      mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    have e6 : 3 * (2 / β) = 6 / β := by ring
    change |gv q (Z i m)| * |gv q (newtonZ q (Z m m) K)| ≤ 3 * (2 / β) at this
    simp only [C]; linarith


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
