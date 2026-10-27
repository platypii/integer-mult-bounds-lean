module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassFrame

/-! Restoration and empty publication frames for the cache-extended caller. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Node

theorem cachedRestoredGroupR_frame {A : ℕ} (R R₀ : Regs 148 A)
    (h93 : R 93 = R₀ 93) (h110 : R 110 = R₀ 110)
    (hhigh : ∀ k : Fin 148, 117 ≤ k.val → R k = R₀ k)
    (hblank : ∀ k : Fin 148, k.val < 117 → k ≠ 93 → k ≠ 110 → R₀ k = []) :
    restoredGroupR R = R₀ := by
  funext k
  by_cases hk93 : k = 93
  · subst k; simpa [restoredGroupR] using h93
  by_cases hk110 : k = 110
  · subst k; simpa [restoredGroupR] using h110
  by_cases hk : k.val < 117
  · simp [restoredGroupR,hk,hk93,hk110,hblank k hk hk93 hk110]
  · simpa [restoredGroupR,hk] using hhigh k (by omega)

theorem cachedPublishedClassR_empty {A : ℕ} (R : Regs 148 A) (h129 : R 129 = []) (h140 : R 140 = []) :
    publishedClassR R (R 132) = Function.update R 128 [] := by
  funext k
  by_cases hk128 : k = 128
  · subst k; simp [publishedClassR]
  by_cases hk129 : k = 129
  · subst k; simp [publishedClassR,h129]
  by_cases hk132 : k = 132
  · subst k; simp [publishedClassR]
  by_cases hk140 : k = 140
  · subst k; simp [publishedClassR,h140]
  simp [publishedClassR,hk128,hk129,hk132,hk140]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
