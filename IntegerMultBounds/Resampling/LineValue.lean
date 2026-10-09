import IntegerMultBounds.Resampling.LineApply
import IntegerMultBounds.Resampling.TableValue
import Mathlib.Data.List.GetD

/-! The line-by-line machine's output read back: the words of line `ℓ` on the
output tape are the `Ã` numerators of that line, with the weights written
by the A-table machine. -/

namespace IntegerMultBounds.Machine.LineApply

open GaussianLine (outWords)
open TwosComplement (signed)
open Resampling.NeumannWords (ext ext_mem ext_length ext_even ext_odd vec outWords_length outWords_even
  outWords_odd val_intCast_toNat)

theorem outs_length (wt arr : List (List Bool)) (s t m p w W L : ℕ) :
    (outs wt arr s t m p w W L).length = 2 * t * L := by
  induction L with
  | zero => rfl
  | succ L ih => rw [outs, List.length_append, ih, outWords_length]; ring

theorem outs_getD (wt arr : List (List Bool)) (s t m p w W L ℓ j : ℕ) (hℓ : ℓ < L) (hj : j < 2 * t) :
    (outs wt arr s t m p w W L).getD (2 * t * ℓ + j) [] =
      (outWords wt (ext s m (line arr s ℓ)) s t m p w W t).getD j [] := by
  induction L with
  | zero => omega
  | succ L ih =>
    rw [outs]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ with h | rfl
    · have : 2 * t * ℓ + j < 2 * t * L := by
        have := Nat.mul_le_mul_left (2 * t) (Nat.succ_le_of_lt h); rw [Nat.mul_succ] at this; omega
      rw [List.getD_append _ _ _ _ (by rw [outs_length]; exact this), ih h]
    · rw [List.getD_append_right _ _ _ _ (by rw [outs_length]; omega), outs_length, Nat.add_sub_cancel_left]

/-- Line `ℓ`, window `k` of the output: the `Ã` numerators of line `ℓ`. -/
theorem line_value (arr : List (List Bool)) (s t m α p w W L : ℕ) [NeZero s] [NeZero t] (hα : 2 ≤ α)
    (hp : 13 ≤ p) (hw : p + 2 ≤ w) (hwW : w ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (harr : arr.length = 2 * s * L) (harrw : ∀ x ∈ arr, x.length = w)
    (harrb : ∀ x ∈ arr, |signed x| ≤ 2 ^ p) (hst : s ≤ t) (ℓ k : ℕ) (hℓ : ℓ < L) (hk : k < t) :
    NLogN.resampANum s t m (Resampling.WindowSum.termW p fun k j => (Resampling.WeightTable.tableA s t α p k j : ℝ) / 2 ^ p)
        (vec s p (line arr s ℓ)) (k : ZMod t) =
      ⟨(signed ((outs (Resampling.TabATape.tabA s t m α p w (t * (2 * m + 1))) arr s t m p w W L).getD
          (2 * t * ℓ + 2 * k) []) : ℝ) / 2 ^ (p + 1),
       (signed ((outs (Resampling.TabATape.tabA s t m α p w (t * (2 * m + 1))) arr s t m p w W L).getD
          (2 * t * ℓ + (2 * k + 1)) []) : ℝ) / 2 ^ (p + 1)⟩ := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  set ys := line arr s ℓ with hys
  have hyl : ys.length = 2 * s := line_length arr s ℓ (by rw [harr]; exact Nat.mul_le_mul_left _ hℓ)
  have hext : ∀ x ∈ ext s m ys, x ∈ arr := fun x hx => line_mem arr s ℓ x (ext_mem s m ys hs hyl x hx)
  set ar : ℤ → ℤ := fun j => signed (ys.getD (2 * (j % s).toNat) [])
  set ai : ℤ → ℤ := fun j => signed (ys.getD (2 * (j % s).toNat + 1) [])
  have hu : ∀ j : ℤ, vec s p ys (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩ := by
    intro j; simp only [vec, val_intCast_toNat s j hs, ar, ai]
  have hre : ∀ q, q < s + 2 * m → signed ((ext s m ys).getD (2 * q) []) = ar ((q : ℤ) - m) := by
    intro q hq; rw [ext_even _ _ _ _ hq]; rfl
  have him : ∀ q, q < s + 2 * m → signed ((ext s m ys).getD (2 * q + 1) []) = ai ((q : ℤ) - m) := by
    intro q hq; rw [ext_odd _ _ _ _ hq]; rfl
  rw [outs_getD _ _ _ _ _ _ _ _ _ _ _ hℓ (by omega), outs_getD _ _ _ _ _ _ _ _ _ _ _ hℓ (by omega),
    outWords_even _ _ _ _ _ _ _ _ _ _ hk, outWords_odd _ _ _ _ _ _ _ _ _ _ hk]
  exact Resampling.TableValue.a_tables s t m α p w W hα hp (ext s m ys) (vec s p ys) ar ai hu hre him hw hwW hW
    (fun x hx => harrw x (hext x hx)) (fun x hx => harrb x (hext x hx)) (by rw [ext_length]) hst k hk

end IntegerMultBounds.Machine.LineApply
