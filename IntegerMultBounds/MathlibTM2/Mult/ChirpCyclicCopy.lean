module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRepeatPrefix
public import IntegerMultBounds.MathlibTM2.Mult.ChirpRotate

/-! # Rotate, copy a repeated prefix, and restore the original source

The inverse rotation uses the length of the complementary interval. All rotation and
repetition workspace is returned empty; only the selected cyclic prefix remains.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def cyclicCopy (frontCount backCount count saved lengthR src front back acc expanded dst buf tmp : Fin T) :
    Pr P T Q A U :=
  .seq (rotatePrefix frontCount src front back tmp) <|
  .seq (repeatPrefix count saved lengthR src acc expanded dst buf tmp)
    (rotatePrefix backCount src front back tmp)

/-- An exact cyclic prefix with the original source, all counters and scratch restored. -/
theorem cyclicCopy_exec {frontCount backCount count saved lengthR src front back acc expanded dst buf tmp : Fin T}
    (hreg : [frontCount, backCount, count, saved, lengthR, src, front, back, acc, expanded, dst, buf, tmp].Nodup)
    (xs ys : List (Fin (A + 4))) (N C : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs ++ ys) (hf : (S.R frontCount).length = xs.length)
    (hb : (S.R backCount).length = ys.length) (hc : (S.R count).length = C)
    (hN : (S.R lengthR).length = N) (hcover : N ≤ C * (xs.length + ys.length))
    (hclean : ∀ k ∈ [saved, front, back, acc, expanded, buf, tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ C * (8 * (xs.length + ys.length) + 9) + 10 * N + 10 * (xs.length + ys.length) + 38 ∧
      Exec body (cyclicCopy frontCount backCount count saved lengthR src front back acc expanded dst buf tmp)
        (mk v S) n (mk v' { S with R := (Function.update S.R dst
          ((repeatStream C (ys ++ xs)).take N ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hr : [count, saved, lengthR, src, acc, expanded, dst, buf, tmp].Nodup := by regs_nodup
  have hrot : [backCount, src, front, back, tmp].Nodup := by regs_nodup
  have hf0 : S.R front = [] := hclean _ (by simp)
  have hb0 : S.R back = [] := hclean _ (by simp)
  have ht0 : S.R tmp = [] := hclean _ (by simp)
  obtain ⟨v₁, hu₁, he₁⟩ := rotatePrefix_exec (body := body) (count := frontCount) (src := src)
    (front := front) (back := back) (tmp := tmp) (by regs_nodup) v S xs ys hsrc hf hf0 hb0 ht0
  let S₁ : Stacks T A := { S with R := Function.update S.R src (ys ++ xs) }
  have off₁ (k : Fin T) (hk : k ≠ src) : S₁.R k = S.R k := by simp [S₁, hk]
  have hclean₁ : ∀ k ∈ [saved, acc, expanded, buf, tmp], S₁.R k = [] := by
    intro k hk
    have hz : S.R k = [] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp)
    have hks : k ≠ src := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        first | assumption | (apply Ne.symm; assumption)
    exact (off₁ k hks).trans hz
  obtain ⟨v₂, n₂, hu₂, hn₂, he₂⟩ := repeatPrefix_exec (body := body) hr v₁ S₁ N C
    (by rw [off₁ _ ‹count ≠ src›]; exact hc) (by rw [off₁ _ ‹lengthR ≠ src›]; exact hN)
    (by simpa [S₁, Nat.add_comm] using hcover) hclean₁
  have hsrc₁ : S₁.R src = ys ++ xs := by simp [S₁]
  rw [hsrc₁] at he₂
  let out := (repeatStream C (ys ++ xs)).take N
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst (out ++ S₁.R dst) }
  have off₂ (k : Fin T) (hk : k ≠ dst) : S₂.R k = S₁.R k := by simp [S₂, hk]
  obtain ⟨v₃, hu₃, he₃⟩ := rotatePrefix_exec (body := body) hrot v₂ S₂ ys xs
    (by simp [S₂, S₁, ‹src ≠ dst›])
    (by rw [off₂ _ ‹backCount ≠ dst›, off₁ _ ‹backCount ≠ src›]; exact hb)
    (by rw [off₂ _ ‹front ≠ dst›, off₁ _ ‹src ≠ front›.symm]; exact hf0)
    (by rw [off₂ _ ‹back ≠ dst›, off₁ _ ‹src ≠ back›.symm]; exact hb0)
    (by rw [off₂ _ ‹dst ≠ tmp›.symm, off₁ _ ‹src ≠ tmp›.symm]; exact ht0)
  have hn : n₂ ≤ C * (8 * (xs.length + ys.length) + 9) + 10 * N + 18 := by
    simpa [S₁, Nat.add_comm] using hn₂
  have hcost : (6 * xs.length + 4 * ys.length + 10) + (n₂ + (6 * ys.length + 4 * xs.length + 10)) ≤
      C * (8 * (xs.length + ys.length) + 9) + 10 * N + 10 * (xs.length + ys.length) + 38 := by
    calc _ ≤ (6 * xs.length + 4 * ys.length + 10) +
        ((C * (8 * (xs.length + ys.length) + 9) + 10 * N + 18) +
          (6 * ys.length + 4 * xs.length + 10)) := Nat.add_le_add_left (Nat.add_le_add_right hn _) _
      _ = _ := by ring
  refine ⟨v₃, _, hu₃.trans (hu₂.trans hu₁), hcost,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hks : k = src
  · subst k
    simp [S₂, S₁, ‹src ≠ dst›, hsrc]
  by_cases hkd : k = dst
  · subst k
    simp [S₂, S₁, ‹src ≠ dst›.symm, out]
  · simp [S₂, S₁, hks, hkd]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
