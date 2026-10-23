module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRepeat

/-! # Copy an exact cyclic-prefix length from whole repeated periods -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def repeatPrefix (count saved lengthR src acc expanded dst buf tmp : Fin T) : Pr P T Q A U :=
  .seq (repeatCopy count saved src acc tmp) <|
  .seq (moveR acc expanded id) <|
  .seq (copyPrefix lengthR expanded dst buf tmp) (uclear expanded)

/-- Repetition overshoot is charged and then discarded; only the selected destination changes. -/
theorem repeatPrefix_exec {count saved lengthR src acc expanded dst buf tmp : Fin T}
    (hreg : [count, saved, lengthR, src, acc, expanded, dst, buf, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (N C : ℕ)
    (hcount : (S.R count).length = C) (hN : (S.R lengthR).length = N)
    (hcover : N ≤ C * (S.R src).length)
    (hclean : ∀ k ∈ [saved, acc, expanded, buf, tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ C * (8 * (S.R src).length + 9) + 10 * N + 18 ∧
      Exec body (repeatPrefix count saved lengthR src acc expanded dst buf tmp) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          ((repeatStream C (S.R src)).take N ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hs0 : S.R saved = [] := hclean _ (by simp)
  have ha0 : S.R acc = [] := hclean _ (by simp)
  have he0 : S.R expanded = [] := hclean _ (by simp)
  have hb0 : S.R buf = [] := hclean _ (by simp)
  have ht0 : S.R tmp = [] := hclean _ (by simp)
  obtain ⟨v₁, n₁, hu₁, hn₁, he₁⟩ := repeatCopy_exec (body := body)
    (count := count) (saved := saved) (src := src) (dst := acc) (tmp := tmp)
    (by regs_nodup) v S hs0 ht0
  let words := repeatStream C (S.R src)
  let S₁ : Stacks T A := { S with R := Function.update S.R acc (words.reverse ++ S.R acc) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body acc expanded ‹acc ≠ expanded› id v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := movedR S₁.R acc expanded id (S₁.R acc) }
  have hx : S₂.R expanded = words := by simp [S₂, S₁, movedR, he0, ha0, ‹acc ≠ expanded›.symm]
  have off (k : Fin T) (ha : k ≠ acc) (he : k ≠ expanded) : S₂.R k = S.R k := by
    simp [S₂, S₁, movedR, ha, he]
  obtain ⟨v₃, hu₃, he₃⟩ := copyPrefix_exec (body := body) (count := lengthR) (src := expanded)
    (dst := dst) (saved := buf) (tmp := tmp) (by regs_nodup) v₂ S₂ (words.take N) (words.drop N)
    (by simpa only [List.take_append_drop] using hx)
    (by rw [off _ ‹lengthR ≠ acc› ‹lengthR ≠ expanded›, hN, List.length_take,
      length_repeatStream, Nat.min_eq_left hcover])
    (by rw [off _ ‹acc ≠ buf›.symm ‹expanded ≠ buf›.symm]; exact hb0)
    (by rw [off _ ‹acc ≠ tmp›.symm ‹expanded ≠ tmp›.symm]; exact ht0)
  let S₃ : Stacks T A := { S₂ with R := Function.update S₂.R dst (words.take N ++ S₂.R dst) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body expanded v₃ S₃
  have hsize : words.length = C * (S.R src).length := length_repeatStream ..
  have hsteps : n₁ + ((2 * (S₁.R acc).length + 2) +
      ((10 * (words.take N).length + 10) + (2 * (S₃.R expanded).length + 2))) ≤
      C * (8 * (S.R src).length + 9) + 10 * N + 18 := by
    rw [hcount] at hn₁
    simp only [S₁, Function.update_self, ha0, List.append_nil, List.length_reverse,
      List.length_take, hsize, Nat.min_eq_left hcover]
    rw [show S₃.R expanded = words by simpa [S₃, ‹expanded ≠ dst›] using hx, hsize]
    nlinarith
  refine ⟨v₄, _, hu₄.trans (hu₃.trans (hu₂.trans hu₁)), hsteps,
    (Exec.seq (by simpa only [hcount] using he₁) (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  clear he₁ he₂ he₃ he₄ hclean
  funext k
  by_cases hke : k = expanded
  · subst k
    simp [S₃, S₂, S₁, movedR, ‹expanded ≠ dst›, he0]
  by_cases hka : k = acc
  · subst k
    simp [S₃, S₂, S₁, movedR, ‹acc ≠ expanded›, ‹acc ≠ dst›, ha0]
  by_cases hkd : k = dst
  · subst k
    simp [S₃, S₂, S₁, movedR, ‹expanded ≠ dst›.symm, ‹acc ≠ dst›.symm, words]
  · simp [S₃, S₂, S₁, movedR, hke, hka, hkd]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
