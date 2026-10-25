module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellShiftReverse
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversedWords
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Execute the second generator from the encoded first column

The row and word counters come from the ordinary L/q headers and are released.
Both source and destination may have borrowed suffixes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateReversedColumn : Pr P₀ 117 Q A U :=
  .seq (umul 2 112 98 104)
    (.seq (.act (pushN 98 (fun _ => tick) 8 .done))
      (.seq (ucopy 102 97 104)
        (.seq (.act (.pop (.rt 97) (fun v _ => v) .done))
          (.seq (shiftReverse 97 99 98 111 113 104 105 106 107) (clearWords [97, 98])))))

/-- The constructor pays for both counters, shifted reversal and release. -/
theorem generateReversedColumn_words_exec (q : ℕ) (x : GaussianInt) (xs : List GaussianInt)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hq : (S.R 112).length = q) (hrows : (S.R 102).length = xs.length + 1)
    (hsrc : S.R 111 = cstream A (2 * q + 8) (x :: xs) ++ tail)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106, 107], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body generateReversedColumn (mk v S)
        (xs.length * (16 * (2 * q + 8) + 21) + 4 * (xs.length + 1) + 12 * (2 * q + 8) + 4 * q + 31)
        (mk v' { S with R := (Function.update S.R 113
          (cstream A (2 * q + 8) (0 :: xs.reverse) ++ S.R 113)) }) := by
  let w := 2 * q + 8
  obtain ⟨v₁, hu₁, he₁⟩ := umul_exec (body := body) 2 (a := 112) (b := 98) (t := 104)
    (by decide) (by decide) (by decide) v S (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 98 (List.replicate (2 * q) tick) }
  have he₁' : Exec body (umul 2 112 98 104) (mk v S) (4 * q + 4) (mk v₁ S₁) := by
    simpa [S₁, hq, hfresh 98 (by simp)] using he₁
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 98 (List.replicate w tick) }
  have he₂ : Exec body (.act (pushN 98 (fun _ => tick) 8 .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    have he := Exec.act (body := body) (pushN 98 (fun _ => tick) 8 .done) (mk v₁ S₁)
    rw [pushN_run] at he
    simpa only [S₂, S₁, Action.run, Function.update_self, List.replicate_append_replicate,
      show 8 + 2 * q = w by dsimp [w]; omega] using he
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec (body := body) (a := 102) (b := 97) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₂ (by simpa [S₂, S₁] using hfresh 104 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 97 (List.replicate (xs.length + 1) tick) }
  have he₃' : Exec body (ucopy 102 97 104) (mk v₁ S₂) (4 * (xs.length + 1) + 4) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hrows, hfresh 97 (by simp)] using he₃
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 97 (List.replicate xs.length tick) }
  have he₄ : Exec body (.act (.pop (.rt 97) (fun v _ => v) .done)) (mk v₃ S₃) 1 (mk v₃ S₄) := by
    have he := Exec.act (body := body) (.pop (.rt 97) (fun v _ => v) .done) (mk v₃ S₃)
    simpa [Action.run, update_rt, S₄, S₃, List.replicate_succ] using he
  obtain ⟨v₅, hu₅, he₅⟩ := shiftReverse_exec (body := body)
    (show [(97 : Fin 117), 99, 98, 111, 113, 104, 105, 106, 107].Nodup by decide)
    w x xs v₃ S₄ tail (by simp [S₄]) (by simpa [S₄, S₃, S₂, S₁] using hsrc)
    (by simp [S₄, S₃, S₂]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₄, S₃, S₂, S₁] using hfresh _ (by simp))
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 113 (cstream A w (0 :: xs.reverse) ++ S₄.R 113) }
  obtain ⟨v₆, hu₆, he₆⟩ := clearWords_exec (body := body) [97, 98] (by decide) v₅ S₅
  have hsum : ([(97 : Fin 117), 98].map (fun k => (S₅.R k).length)).sum = xs.length + w := by
    simp [S₅, S₄, S₃, S₂]
  refine ⟨v₆, hu₆.trans (hu₅.trans (hu₃.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast ?_ ?_⟩
  · rw [hsum]; dsimp [w]; ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ho : k = 113
    · subst k; simp [S₅, S₄, S₃, S₂, S₁, w]
    by_cases h97 : k = 97
    · subst k; simp [hfresh 97 (by simp)]
    by_cases h98 : k = 98
    · subst k; simp [hfresh 98 (by simp)]
    simp [S₅, S₄, S₃, S₂, S₁, ho, h97, h98]

/-- Instantiate the structural caller with the first generator's runtime words. -/
theorem generateReversedColumn_exec {P s t u band L q n : ℕ} (hL : 0 < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hq : (S.R 112).length = q) (hrows : (S.R 102).length = L)
    (hsrc : S.R 111 = cstream A (2 * q + 8) (columnWords P s t u band L q n) ++ tail)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106, 107], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body generateReversedColumn (mk v S)
        ((L - 1) * (16 * (2 * q + 8) + 21) + 4 * L + 12 * (2 * q + 8) + 4 * q + 31)
        (mk v' { S with R := (Function.update S.R 113
          (cstream A (2 * q + 8) (reversedColumnWords P s t u band L q n) ++ S.R 113)) }) := by
  cases hx : columnWords P s t u band L q n with
  | nil =>
    have hlen := columnWords_length P s t u band L q n
    rw [hx] at hlen
    simp only [List.length_nil] at hlen
    omega
  | cons x xs =>
    have hlen : xs.length + 1 = L := by
      simpa only [hx, List.length_cons] using columnWords_length P s t u band L q n
    obtain ⟨v', hu, he⟩ := generateReversedColumn_words_exec (body := body) q x xs v S tail hq
      (by omega) (by simpa only [hx] using hsrc) hfresh
    have hwords : reversedColumnWords P s t u band L q n = 0 :: xs.reverse := by
      rw [reversedColumnWords_eq hL, hx]
      rfl
    rw [hlen, show xs.length = L - 1 by omega] at he
    exact ⟨v', hu, by simpa only [hwords] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
