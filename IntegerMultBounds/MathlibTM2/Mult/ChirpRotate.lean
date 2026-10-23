module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! # Counted rotation of a coefficient stream

Save the first interval, reverse the remaining interval into a second workspace, and
move both back. Words stay in their original symbol order; only the source changes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def rotatePrefix (count src front back tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer count src front tmp) <|
  .seq (moveR src back id) <|
  .seq (moveR front src id) (moveR back src id)

/-- Rotate a counted prefix to the end and restore all counters and scratch. -/
theorem rotatePrefix_exec {count src front back tmp : Fin T}
    (hreg : [count, src, front, back, tmp].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (xs ys : List (Fin (A + 4)))
    (hsrc : S.R src = xs ++ ys) (hlen : (S.R count).length = xs.length)
    (hfront : S.R front = []) (hback : S.R back = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (rotatePrefix count src front back tmp) (mk v S)
        (6 * xs.length + 4 * ys.length + 10)
        (mk v' { S with R := Function.update S.R src (ys ++ xs) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := transfer_exec (body := body) (count := count) (src := src) (dst := front) (tmp := tmp) (by regs_nodup) v S xs ys hsrc hlen htmp
  let S₁ : Stacks T A := { S with R := Function.update (Function.update S.R src ys) front (xs.reverse ++ S.R front) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body src back ‹src ≠ back› id v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := movedR S₁.R src back id (S₁.R src) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body front src ‹src ≠ front›.symm id v₂ S₂
  let S₃ : Stacks T A := { S₂ with R := movedR S₂.R front src id (S₂.R front) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body back src ‹src ≠ back›.symm id v₃ S₃
  refine ⟨v₄, hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast ?_ ?_⟩
  · simp (disch := first | assumption | (apply Ne.symm; assumption))
      [S₃, S₂, S₁, movedR, hfront, hback]
    ring
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₃ he₄
    funext k
    simp only [S₃, S₂, S₁, movedR, Function.update_apply, List.map_id,
      hfront, hback, List.append_nil]
    split_ifs <;> subst_vars <;> simp_all only [ne_eq, eq_self, not_true_eq_false, not_false_eq_true, List.append_nil, List.reverse_reverse]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
