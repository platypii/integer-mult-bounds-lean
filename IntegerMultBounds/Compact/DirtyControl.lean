import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
The four *integer* updates in compact-control-movement.tex. These statements
hold for arbitrary dirty integer temporaries, not merely enumerated examples.
The packed modular implementation and its no-carry refinement remain separate
obligations; this file does not assert a tape-runtime bound.
-/

namespace IntegerMultBounds.Compact

def toggle (v z : ℤ) : ℤ := v + z * (1 - 2 * (v % 2))

def fourUpdate (v w z : ℤ) : ℤ × ℤ :=
  let v₁ := v + 2 * z * w
  let w₁ := w + v₁ % 2
  let v₂ := v₁ + z * (1 - 2 * w₁)
  let w₂ := w₁ - ((v₂ % 2 + z) % 2)
  (v₂, w₂)

theorem fourUpdate_eq (v w z : ℤ) (hz : z = 0 ∨ z = 1) :
    fourUpdate v w z = (toggle v z, w) := by
  rcases hz with rfl | rfl <;>
    simp only [fourUpdate, toggle, mul_zero, zero_mul, add_zero, mul_one, one_mul] <;>
    congr 1 <;> omega

theorem toggle_parity (v z : ℤ) (hz : z = 0 ∨ z = 1) :
    toggle v z % 2 = (v % 2 + z) % 2 := by
  rcases hz with rfl | rfl <;>
    simp only [toggle, zero_mul, add_zero, one_mul] <;> omega

theorem toggle_guard (v z : ℤ) (hz : z = 0 ∨ z = 1) :
    toggle v z / 2 = v / 2 := by
  rcases hz with rfl | rfl <;>
    simp only [toggle, zero_mul, add_zero, one_mul]
  all_goals omega

theorem toggle_twice (v z : ℤ) (hz : z = 0 ∨ z = 1) :
    toggle (toggle v z) z = v := by
  rcases hz with rfl | rfl <;>
    simp only [toggle, zero_mul, add_zero, one_mul]
  all_goals omega

/-- The two dirty-control parities implement the later-source XOR. -/
theorem later_source (v u x : ℤ) (hx : x = 0 ∨ x = 1) :
    toggle (toggle v (u % 2)) ((u + x) % 2) = toggle v x := by
  have hu : u % 2 = 0 ∨ u % 2 = 1 := by omega
  have hnext : (u + 1) % 2 = 1 - u % 2 := by omega
  rcases hx with rfl | rfl <;> rcases hu with hu | hu
  all_goals simp only [toggle, add_zero, hnext, hu, sub_zero, sub_self,
    zero_mul, one_mul]
  all_goals omega

/-- The guarded integer implementation never leaves its segment or temp digit. -/
theorem guarded_updates (B L g a w z : ℤ)
    (hB : 1 ≤ B) (hg₀ : 2 * B ≤ g) (hg₁ : g < L - 2 * B)
    (ha : a = 0 ∨ a = 1) (hw₀ : 0 ≤ w) (hw₁ : w < B - 1)
    (hz : z = 0 ∨ z = 1) :
    let v := 2 * g + a
    let v₁ := v + 2 * z * w
    let w₁ := w + v₁ % 2
    let v₂ := v₁ + z * (1 - 2 * w₁)
    0 ≤ v₁ ∧ v₁ < 2 * L ∧ 0 ≤ w₁ ∧ w₁ < B ∧
      0 ≤ v₂ ∧ v₂ < 2 * L := by
  rcases ha with rfl | rfl <;> rcases hz with rfl | rfl <;> dsimp <;> omega

end IntegerMultBounds.Compact
