module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandBounds
public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableWordBounds

/-! # Aligned weighted chirp streams

All windows of a line are multiplied in one stream traversal. The table has one row
per block, since its weights depend on the block origin. No per-block multiplier setup
or supplied coefficient-count tape is needed.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- A real input-weight row in exactly the order emitted by table generation. -/
def chirpWeightRow (s t α q m n : ℕ) : List GaussianInt :=
  (List.range (3 * m + 1)).map fun a : ℕ =>
    ⟨chirpInputNumerators s t α q m (n * m) a, 0⟩

@[simp] theorem length_chirpWeightRow (s t α q m n : ℕ) :
    (chirpWeightRow s t α q m n).length = 3 * m + 1 := by simp [chirpWeightRow]

/-- Aligned row concatenation commutes with pointwise multiplication. -/
theorem zipWith_flatMap_rows {α β γ δ : Type} (f : β → γ → δ)
    (x : α → List β) (y : α → List γ) (ls : List α)
    (hlen : ∀ a ∈ ls, (x a).length = (y a).length) :
    List.zipWith f (ls.flatMap x) (ls.flatMap y) =
      ls.flatMap (fun a => List.zipWith f (x a) (y a)) := by
  induction ls with
  | nil => simp
  | cons a ls ih =>
    simp only [List.flatMap_cons]
    rw [List.zipWith_append (hlen a (by simp)), ih (fun b hb => hlen b (by simp [hb]))]

/-- The single aligned multiplier traversal produces the forward weighted operand rows. -/
theorem chirpWeightedStream_eq {s t q m M : ℕ} (α : ℕ) (hs : 0 < s)
    (hn : ∀ n < M, n * m < t) (u : ZMod s → GaussianInt) :
    List.zipWith (fun x y => tdivN q (x * y))
      ((List.range M).flatMap fun n => chirpWindow s t m n u)
      ((List.range M).flatMap fun n => chirpWeightRow s t α q m n) =
      (List.range M).flatMap (fun n => chirpWeighted s t q m n
        (chirpInputNumerators s t α q m) u) := by
  rw [zipWith_flatMap_rows _ _ _ _ (by
    intro n hn'
    rw [length_chirpWindow hs (hn n (List.mem_range.mp hn')), length_chirpWeightRow])]
  apply List.flatMap_congr
  intro n hn'
  exact (chirpWeighted_eq_zipWith hs (hn n (List.mem_range.mp hn')) _ u).symm

/-- A decoded disk bound provides both signed component bounds for multiplication. -/
theorem fits_of_norm_value_le {q w : ℕ} (hw : q + 2 ≤ w) (x : GaussianInt)
    (hx : ‖value q x‖ ≤ 1) : Fits w x := by
  have h := disk_of_norm_value_le q x hx
  have he : (2 : ℤ) ^ (2 * q) = (2 ^ q) ^ 2 := by rw [pow_mul']
  rw [he] at h
  have hp : (0 : ℤ) ≤ 2 ^ q := by positivity
  have hlt : (2 : ℤ) ^ q < 2 ^ (w - 1) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  constructor
  · exact (_root_.abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg x.im]) hp)).trans_lt hlt
  · exact (_root_.abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg x.re]) hp)).trans_lt hlt

/-- Generated real table numerators fit the multiplier word with three guard bits. -/
theorem chirpWeightRow_fits {s t α q w m n : ℕ} (hq : 13 ≤ q)
    (ht : 0 < t) (hα : 0 < α) (hw : q + 3 ≤ w)
    (y : GaussianInt) (hy : y ∈ chirpWeightRow s t α q m n) : Fits w y ∧ y.im = 0 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hy
  have hbound := expPiNat_neg_le q (chirpGN s t m (n * m) a) (chirpKD t α)
    hq (by unfold chirpKD; positivity)
  have htwo : 2 ≤ 2 ^ q := by
    exact (by norm_num : 2 ≤ 2 ^ 13).trans (Nat.pow_le_pow_right (by decide) hq)
  have hsum : 2 ^ q + 2 ≤ 2 ^ (q + 1) := by rw [pow_succ]; omega
  have hlt : chirpTableG s t α q m (n * m) a < 2 ^ (w - 1) :=
    (hbound.trans hsum).trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  constructor
  · constructor
    · change |(chirpTableG s t α q m (n * m) a : ℤ)| < _
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast hlt
    · change |(0 : ℤ)| < _
      simp only [abs_zero]
      positivity
  · rfl

/-- Every gathered window coefficient fits whenever the original grid input is in the disk. -/
theorem chirpWindow_fits {s t q w m n : ℕ} (hs : 0 < s) (hn : n * m < t)
    (hw : q + 2 ≤ w) (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (x : GaussianInt) (hx : x ∈ chirpWindow s t m n u) : Fits w x := by
  obtain ⟨a, ha, rfl⟩ := List.mem_iff_getElem.mp hx
  have ha' : a < 3 * m + 1 := by rwa [length_chirpWindow hs hn] at ha
  have harg := chirpWindow_getD hs hn ha' u
  rw [List.getD_eq_getElem _ _ ha] at harg
  rw [harg]
  exact fits_of_norm_value_le hw _ (hu _)

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
