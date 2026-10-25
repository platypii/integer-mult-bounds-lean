module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReciprocal
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerColumnAccuracy

/-! # Obtain the actual reciprocal word from an executed integer column -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- The signed context returned by the column generator supplies the positive
binary divisor and all clean division workspace. No reciprocal data are assumed. -/
theorem generateIntegerReciprocal_exec {P s t u band L n q W : ℕ}
    (hA : 4 ≤ A) (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hL : 0 < L) (hn : 1 ≤ n) (hd : q + P * n < W) (hw : 2 * q + 8 ≤ W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailF : List (Fin (A + 4)))
    (hctx : IntegerGeneratorContext P s t u band L n W tailX tailF S)
    (hq : (S.R 112).length = q) :
    ∃ v' m, v'.user = v.user ∧ m ≤ W * (12 * W + 128) + 6 * (2 * q + 8) + 4 * q + 134 ∧
      Exec body generateReciprocal (mk v S) m
        (mk v' { S with R := Function.update S.R 96 (csyms A (2 * q + 8) (reciprocalWord P s t u band L q n)) }) := by
  let corner := (columnNumerators P s t u band L n).getD 0 0
  have hc : 0 < corner := columnNumerators_corner_pos hP hs hst hu hL hn
  let y := corner.toNat
  have hycast : (y : ℤ) = corner := Int.toNat_of_nonneg hc.le
  have hy0 : 0 < y := by omega
  have hlow (k : Fin 117) (hk : k.val < 64) : S.R k = [] := by
    have h := (hctx.row.clean ⟨k.val, hk⟩).2
    simpa [mul] using h
  have hfresh : ∀ k ∈ [(0 : Fin 117), 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12,
      96, 97, 98, 99, 104, 105, 106, 107, 115], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hctx.rest
      | exact hctx.exponent
      | exact hlow _ (by decide)
      | exact hctx.row.work _ (by simp [integerRowWork])
  cases hxs : rowColumnWords P s t u band L n with
  | nil =>
    have hlen := hctx.row.length
    rw [hxs] at hlen
    simp only [List.length_nil] at hlen
    omega
  | cons z zs =>
    have hz : z = (⟨corner, 0⟩ : GaussianInt) := by
      simpa [hxs, corner] using rowColumnWords_getD P s t u band L n 0 hL
    have hfit := (hctx.row.fits z (by simp [hxs])).1
    have hyInt : (y : ℤ) < (2 : ℤ) ^ W := by
      rw [hz] at hfit
      change |corner| < (2 : ℤ) ^ (W - 1) at hfit
      rw [hycast]
      exact (le_abs_self corner).trans_lt (hfit.trans_le
        (pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) (by omega)))
    have hy : y < 2 ^ W := by exact_mod_cast hyInt
    have hden : S.R 110 = csyms A W (⟨(y : ℤ), 0⟩ : GaussianInt) ++ (cstream A W zs ++ tailX) := by
      rw [hctx.row.column, hxs, hz, cstream_cons, List.append_assoc, hycast]
    obtain ⟨v', m, hu', hm, he⟩ := generateReciprocal_exec (body := body) hA P n q W y hn hd hw hy hy0
      v S _ hctx.precision hctx.iteration hq hctx.row.width hden hfresh
    have hword : (⟨(((2 ^ (q + P * n)) / y : ℕ) : ℤ), 0⟩ : GaussianInt) =
        reciprocalWord P s t u band L q n := by
      rw [← integerReciprocalWord_eq hP hs hst hu hL hn]
      simp [integerReciprocalWord, Int.natCast_ediv, hycast, corner]
    exact ⟨v', m, hu', hm, by simpa only [hword] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
