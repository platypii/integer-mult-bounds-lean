module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedIndex
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing

/-! # Requested accuracy of the published real interior cell

This compares the actual published words with a solution of the original
ambient principal system. Cell geometry and maximality stay explicit; no halo
size is substituted for an ambient parameter.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

/-- The published real cell has the requested final accuracy, rather than only
accuracy for its intermediate arithmetic stages. -/
theorem publishedCell_accuracy {A M L s t p u l j rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hA : 4 ≤ A) (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value (executionPrecision p l j rhsExp) (C n k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (n : Fin M) (I : Finset (ZMod s)) (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) I x
      (fun k => (value (executionPrecision p l j rhsExp) (C n k)).re))
    (hfit : (lo n).val + L ≤ s)
    (hint : ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo n + (k : ZMod s)) ∧ lo n + (k : ZMod s) ∈ I)
    (hcell : ∀ k < L, cell s t (lo n + (k : ZMod s)) = cell s t (lo n))
    (hmax : ∀ k ∈ I, cell s t k = cell s t (lo n) → ∃ i < L, lo n + (i : ZMod s) = k)
    (i : Fin L) (tail : List (Fin (A + 4))) :
    let q := executionPrecision p l j rhsExp
    let w := executionWidth p l j rhsExp
    let stage := executionStagePrecision p l j rhsExp
    let cExp := sourceExponent l j rhsExp
    |(value q (decodeWord (((cstream A w
        (publishedWords M L (executedOutputWords s t p u q l M L stage cExp lo C)) ++ tail).drop
          ((n.val * L + i.val) * w)).take w))).re - x (lo n + (i.val : ZMod s))| ≤ 1 / (2 : ℝ) ^ j := by
  dsimp only
  let q := executionPrecision p l j rhsExp
  let w := executionWidth p l j rhsExp
  let stage := executionStagePrecision p l j rhsExp
  let b := executionExponent p l j rhsExp
  let cExp := sourceExponent l j rhsExp
  let R := executedRun s t p u q l w M L stage cExp lo C n tail
  have hvalid := executedRun_sized_valid hA hp hst.le hu hαu hθ hgap hbudget hL hpad lo C hC n tail
  rcases hvalid with ⟨hr, hv, hvV, hxh, hzh, hw, hu₁, hu₂, hu₃, hu₄, hout, hy⟩
  have hpow : 0 < (2 : ℕ) ^ l := by positivity
  have hLN : L ≤ 2 ^ l := by omega
  have hstage : l ≤ stage := by
    dsimp [stage, executionStagePrecision, executionExponent, inputExponent, sourceExponent]
    omega
  have hLη : (L : ℝ) * (1 / (2 : ℝ) ^ stage) ≤ 1 := by
    rw [mul_one_div]
    apply (div_le_one (by positivity)).2
    exact (by exact_mod_cast hLN : (L : ℝ) ≤ (2 : ℝ) ^ l).trans
      (pow_le_pow_right₀ (by norm_num) hstage)
  have hc : ∀ k < L,
      |(value q (C n (lo n + (k : ZMod s)))).re| ≤ (2 : ℝ) ^ cExp := by
    intro k _
    exact (Complex.abs_re_le_norm _).trans ((hC n n.isLt _).trans
      (pow_le_pow_right₀ (by norm_num) (by dsimp [cExp, sourceExponent]; omega)))
  have herr := rounded_cell s t hst p u hp hu hαu hθ hgap hbudget I x
    (fun k => (value q (C n k)).re) hx (lo n) L hL hfit hint hcell hmax
    R.xh R.zh R.r R.v R.u₁ R.u₂ R.u₃ R.u₄ R.out R.y R.w
    (1 / (2 : ℝ) ^ stage) ((2 : ℝ) ^ cExp) ((2 : ℝ) ^ b)
    (by positivity) (by positivity) (one_le_pow₀ (by norm_num)) hLη hc
    hr hv hvV hxh hzh hw hu₁ hu₂ hu₃ hu₄ hout hy i i.isLt
  have hread := executedRun_y_published s t p u q l w M L stage cExp lo C n i tail
  change R.y i = _ at hread
  rw [hread] at herr
  exact herr.trans (execution_cell_error p l j rhsExp L hpad)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
