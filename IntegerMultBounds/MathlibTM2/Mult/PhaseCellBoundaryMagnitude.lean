module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStableInteriorBounds
public import IntegerMultBounds.NLogN.PhaseCellHaloBoundary

/-! A boundary output's storage magnitude follows from its proved forward accuracy. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloBoundary_norm {s t p u q rhsExp a b : ℕ} [NeZero s] {α d ε : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (B C : ZMod s → GaussianInt) (hB : ∀ i, ‖value q (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hCreal : ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b, (C i).im = 0)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) (haloVertices s a b) x (fun i => (value q (B i)).re))
    (hε : ε ≤ 1)
    (herror : PhaseCellInterface.ErrorOn (haloBoundary s t (PhaseCellBand.width p u) a b)
      (fun i => (value q (C i)).re) x ε) :
    ∀ i ∈ haloBoundary s t (PhaseCellBand.width p u) a b,
      ‖value q (C i)‖ ≤ (2 : ℝ)^stableInteriorExponent p rhsExp := by
  let : NeZero t := ⟨by omega⟩
  have hsubset : haloBoundary s t (PhaseCellBand.width p u) a b ⊆ haloVertices s a b := by
    intro i hi
    exact (Finset.mem_sdiff.mp hi).1
  have hnorm := stableSolve_norm (by omega : 0 < p) (haloVertices s a b)
    (haloBoundary s t (PhaseCellBand.width p u) a b) hsubset
    (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget) B C hB x hx
    (fun i hi => (herror i hi).trans hε)
  intro i hi
  have hreal : realPartWord (C i) = C i := by
    ext <;> simp [realPartWord,hCreal i hi]
  simpa only [hreal] using hnorm i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
