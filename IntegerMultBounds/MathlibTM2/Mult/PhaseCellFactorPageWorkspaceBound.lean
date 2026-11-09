module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledFactorPageStock
import Mathlib.Tactic.Ring

/-! The complete factor page uses space proportional to its banded output volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem factorPageWorkspace_le (q W N : ℕ) :
    factorPageWorkspace q W N ≤ 20000*(N+W+1)*(W+1)*(q+1) := by
  unfold factorPageWorkspace factorInputsWorkspace factorWindowWorkspace
    factorSlidingStepWorkspace factorRowWorkspace factorWordUniformWorkspace
    copyPackedWordCost feedFactorWordCost factorZeroEntryCost
  dsimp only
  ring_nf
  omega

theorem scaledGeneratedFactorPageWorkspace24_le (q band N : ℕ) :
    scaledGeneratedFactorPageWorkspace 24 q band N ≤
      14000000*(N+band+1)*(band+1)*(q+1) := by
  have h := factorPageWorkspace_le q (24*band+1) N
  unfold scaledGeneratedFactorPageWorkspace
  ring_nf at h ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
