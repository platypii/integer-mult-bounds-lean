module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyAfterPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ChirpReverse

/-! # Construct one factor row from a retained distance vector -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def constructFactorRow : Pr P₀ 117 Q A U :=
  .seq (copyAfterPrefix 94 100 110 109 104 105 106)
    (reverseWords 98 107 94 110 109 104 105 106)

/-- The distance vector, both count headers and arbitrary suffixes are retained. -/
theorem constructFactorRow_words_exec (L W i : ℕ) (hi : i < L) (xs : List GaussianInt)
    (hL : xs.length = L) (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hW : (S.R 94).length = W) (hleft : (S.R 98).length = i + 1)
    (hright : (S.R 100).length = (L - i - 1) * W)
    (hsrc : S.R 110 = cstream A W xs ++ tail)
    (hfresh : ∀ k ∈ [(104 : Fin 117), 105, 106, 107], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body constructFactorRow (mk v S)
        (6 * W + 10 * ((L - i - 1) * W) + 16 + ((i + 1) * (16 * W + 19) + 6))
        (mk v' { S with R := (Function.update S.R 109
          (cstream A W ((xs.take (i + 1)).reverse ++ (xs.drop 1).take (L - i - 1)) ++ S.R 109)) }) := by
  cases xs with
  | nil => simp only [List.length_nil] at hL; omega
  | cons x xs =>
    have hlen : xs.length + 1 = L := hL
    let r := L - i - 1
    have hr : r ≤ xs.length := by dsimp [r]; omega
    have hleftCount : i + 1 ≤ (x :: xs).length := by simp only [List.length_cons]; omega
    have hsplit : cstream A W xs = cstream A W (xs.take r) ++ cstream A W (xs.drop r) := by
      rw [← cstream_append, List.take_append_drop]
    obtain ⟨v₁, hu₁, he₁⟩ := copyAfterPrefix_exec (body := body)
      (show [(94 : Fin 117), 100, 110, 109, 104, 105, 106].Nodup by decide)
      v S (csyms A W x) (cstream A W (xs.take r)) (cstream A W (xs.drop r) ++ tail)
      (by simpa [cstream_cons, hsplit, List.append_assoc] using hsrc)
      (by simpa using hW) (by simp [hright, List.length_take, Nat.min_eq_left hr, r])
      (hfresh 104 (by simp)) (hfresh 105 (by simp)) (hfresh 106 (by simp))
    let S₁ : Stacks 117 A := { S with R := Function.update S.R 109 (cstream A W (xs.take r) ++ S.R 109) }
    have hsplit' : cstream A W (x :: xs) =
        cstream A W ((x :: xs).take (i + 1)) ++ cstream A W ((x :: xs).drop (i + 1)) := by
      rw [← cstream_append, List.take_append_drop]
    obtain ⟨v₂, hu₂, he₂⟩ := reverseWords_coeffs_exec (body := body)
      (show [(98 : Fin 117), 107, 94, 110, 109, 104, 105, 106].Nodup by decide)
      W ((x :: xs).take (i + 1)) v₁ S₁ (cstream A W ((x :: xs).drop (i + 1)) ++ tail)
      (by simp [S₁, hleft, List.length_take, Nat.min_eq_left hleftCount] <;> omega)
      (by simpa [S₁, hsplit', List.append_assoc] using hsrc)
      (by simpa [S₁] using hW) (by simpa [S₁] using hfresh 107 (by simp))
      (by simpa [S₁] using hfresh 104 (by simp)) (by simpa [S₁] using hfresh 105 (by simp))
      (by simpa [S₁] using hfresh 106 (by simp))
    refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast ?_ ?_⟩
    · simp [List.length_take, Nat.min_eq_left hleftCount, Nat.min_eq_left hr, r]
      omega
    · congr 1
      ext1
      · rfl
      · rfl
      · rfl
      funext k
      by_cases hk : k = 109
      · subst k; simp [S₁, cstream_append, List.append_assoc, r]
      simp [S₁, hk]

/-- Instantiate the row constructor with the actual Toeplitz coefficients. -/
theorem constructFactorRow_exec (P s t u band L W i : ℕ) (hi : i < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hW : (S.R 94).length = W) (hleft : (S.R 98).length = i + 1)
    (hright : (S.R 100).length = (L - i - 1) * W)
    (hsrc : S.R 110 = cstream A W (distanceFactorWords P s t u band L) ++ tail)
    (hfresh : ∀ k ∈ [(104 : Fin 117), 105, 106, 107], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 16 * (L * W) + 19 * L + 6 * W + 22 ∧
      Exec body constructFactorRow (mk v S) m
        (mk v' { S with R := Function.update S.R 109 (cstream A W (rowFactorWords P s t u band L i) ++ S.R 109) }) := by
  obtain ⟨v', hu, he⟩ := constructFactorRow_words_exec (body := body) L W i hi _ (by simp)
    v S tail hW hleft hright hsrc hfresh
  refine ⟨v', 6 * W + 10 * ((L - i - 1) * W) + 16 + ((i + 1) * (16 * W + 19) + 6), hu, ?_, ?_⟩
  · have hcount : i + 1 + (L - i - 1) = L := by omega
    nlinarith
  · simpa only [← rowFactorWords_from_distances P s t u band L i hi] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
