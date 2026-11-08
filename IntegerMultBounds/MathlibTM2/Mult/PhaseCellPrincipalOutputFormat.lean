module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutionSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedAmbient

/-! A real accurate principal output fits words by stability, regardless of its construction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem principalOutput_format {s t p u q w rhsExp : ℕ} [NeZero s]
    (hp : 0 < p) (active : Finset (ZMod s))
    (hw : q+stableInteriorExponent p rhsExp+2 ≤ w)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (C G : ZMod s → GaussianInt) (hC : ∀ i, ‖value q (C i)‖ ≤ (2 : ℝ)^rhsExp)
    (hreal : ∀ i, (G i).im = 0) (hoff : ∀ i ∉ active, G i = 0)
    (x : ZMod s → ℝ) (hx : SchurDominance.Solves (realMatrix s t p u) active x
      (fun i => (value q (C i)).re))
    (herror : PhaseCellInterface.ErrorOn active (fun i => (value q (G i)).re) x 1) :
    (∀ i, ‖value q (G i)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp) ∧
    (∀ i, Fits w (G i)) := by
  have hnorm (i : ZMod s) : ‖value q (G i)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
    by_cases hi : i ∈ active
    · have h := stableSolve_norm hp active active (Finset.Subset.refl _) hdom C G hC x hx herror i hi
      have heq : realPartWord (G i) = G i := by
        apply Zsqrtd.ext <;> simp [realPartWord,hreal i]
      rwa [heq] at h
    · rw [hoff i hi]
      have hz : value q (0 : GaussianInt) = 0 := by apply Complex.ext <;> simp [value]
      rw [hz,norm_zero]
      positivity
  exact ⟨hnorm,fun i => fits_of_value_power hw (G i) (hnorm i)⟩

theorem execution_stable_output_width (p l j rhsExp : ℕ) :
    executionPrecision p l j rhsExp+stableInteriorExponent p rhsExp+2 ≤ executionWidth p l j rhsExp := by
  unfold executionPrecision executionWidth executionExponent inputExponent sourceExponent stableInteriorExponent
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
