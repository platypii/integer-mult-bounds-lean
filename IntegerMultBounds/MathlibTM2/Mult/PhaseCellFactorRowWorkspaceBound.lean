module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowStock
import Mathlib.Tactic.GCongr

/-! Factor-row workspace is monotone in the borrowed rank headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem factorWordUniformWorkspace_mono (q W N a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d) :
    factorWordUniformWorkspace q a c W N ≤ factorWordUniformWorkspace q b d W N := by
  unfold factorWordUniformWorkspace
  gcongr

theorem factorRowWorkspace_mono (q W N a b c d : ℕ) (hab : a ≤ b) (hcd : c ≤ d) :
    factorRowWorkspace q W N a c ≤ factorRowWorkspace q W N b d := by
  have hword := factorWordUniformWorkspace_mono q W N (a+(2*W+1)) (b+(2*W+1)) c d
    (Nat.add_le_add_right hab _) hcd
  unfold factorRowWorkspace
  dsimp only
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
