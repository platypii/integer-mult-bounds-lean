module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.NLogN.PhaseCellConcreteSolve

/-! The existing rounded phase-cell solver inhabits the shared numerical endpoint.
An S1 implementation must establish the same endpoint through stage error bounds;
it need not reproduce this particular scalar-rounding implementation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix Finset

/-- Anchor the S3/S4/S5 endpoint to the checked full-line reference solve. -/
theorem pcSolve_spec {s t : ℕ} [NeZero s] [NeZero t] (hst : s < t)
    {α d : ℝ} (hα : 0 < α) (p u : ℕ) (hp : 2 ≤ p) (hwidth : 8 * p ≤ 2 ^ u)
    (hαu : α ^ 2 = (u : ℝ)) (hθ : 1 / (4 * (p : ℝ)) ≤ (t : ℝ) / s - 1)
    (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (I : Finset (ZMod s)) (hI : ∀ i, i ∈ I ↔ Interior s t (PhaseCellBand.width p u) i)
    (rd : ℝ → ℝ) (η : ℝ) (hrd : ∀ x, |rd x - x| ≤ η) (hrd0 : rd 0 = 0) (K : ℕ)
    (hK : (1 - 1 / (32 * (p : ℝ)) / 4 / 2) ^ (2 ^ K) ≤ 3 * (5 * η) / (1 / (32 * (p : ℝ)) / 4))
    (hprec : 2 ^ (8 * p + 46) * (p : ℝ) ^ 7 * (s : ℝ) ^ 2 * η ≤ 1 / 2) :
    SolveSpec (realMatrix s t p u) univ univ (1 / 2)
      (pcSolve s t p u rd K I) (2 ^ (8 * p + 46) * (p : ℝ) ^ 7 * (s : ℝ) ^ 2 * η) := by
  intro x b hx hb i _
  have hsystem : Matrix.mulVec (realMatrix s t p u) x = b := by
    funext k
    simpa [Matrix.mulVec, dotProduct] using hx k (mem_univ k)
  simpa only [Real.norm_eq_abs] using
    pcSolve_error s t p u hst hα hp hwidth hαu hθ hgap hbudget I hI rd η hrd hrd0 K hK hprec
      x b hsystem (fun k => hb k (mem_univ k)) i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
