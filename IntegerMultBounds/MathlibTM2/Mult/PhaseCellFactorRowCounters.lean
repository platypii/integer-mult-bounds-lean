module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowConstruct
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Generate and release each factor row's prefix counters -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def factorRowStep : Pr P₀ 117 Q A U :=
  .seq (ucopy 97 98 104)
    (.seq (.act (pushN 98 (fun _ => tick) 1 .done))
      (.seq (ucopy 102 99 104)
        (.seq (usub 98 99 104)
          (.seq (unaryProduct 99 94 100 104 105)
            (.seq constructFactorRow
              (.seq (clearWords [98, 99, 100]) (.act (pushN 97 (fun _ => tick) 1 .done))))))))

def factorRowStepCost (L W : ℕ) : ℕ := 24 * (L * W) + 48 * L + 6 * W + 48

theorem factorRowStep_exec (P s t u band L W i : ℕ) (hi : i < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hW : (S.R 94).length = W) (hL : (S.R 102).length = L) (hiR : (S.R 97).length = i)
    (hsrc : S.R 110 = cstream A W (distanceFactorWords P s t u band L) ++ tail)
    (hfresh : ∀ k ∈ [(98 : Fin 117), 99, 100, 104, 105, 106, 107], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ factorRowStepCost L W ∧
      Exec body factorRowStep (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 109
          (cstream A W (rowFactorWords P s t u band L i) ++ S.R 109)) 97 (tick :: S.R 97)) }) := by
  let r := L - i - 1
  obtain ⟨v₁, hu₁, he₁⟩ := ucopy_exec (body := body) (a := 97) (b := 98) (t := 104)
    (by decide) (by decide) (by decide) v S (hfresh 104 (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 98 (List.replicate i tick) }
  have he₁' : Exec body (ucopy 97 98 104) (mk v S) (4 * i + 4) (mk v₁ S₁) := by
    simpa [S₁, hiR, hfresh 98 (by simp)] using he₁
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 98 (List.replicate (i + 1) tick) }
  have he₂ : Exec body (.act (pushN 98 (fun _ => tick) 1 .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    have he := Exec.act (body := body) (pushN 98 (fun _ => tick) 1 .done) (mk v₁ S₁)
    rw [pushN_run] at he
    rw [show S₁.R 98 = List.replicate i tick by simp [S₁], List.replicate_append_replicate,
      show 1 + i = i + 1 by omega] at he
    exact he
  obtain ⟨v₃, hu₃, he₃⟩ := ucopy_exec (body := body) (a := 102) (b := 99) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₂ (by simpa [S₂, S₁] using hfresh 104 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 99 (List.replicate L tick) }
  have he₃' : Exec body (ucopy 102 99 104) (mk v₁ S₂) (4 * L + 4) (mk v₃ S₃) := by
    simpa [S₃, S₂, S₁, hL, hfresh 99 (by simp)] using he₃
  obtain ⟨v₄, hu₄, he₄⟩ := usub_exec (body := body) (a := 98) (b := 99) (t := 104)
    (by decide) (by decide) (by decide) v₃ S₃ (by simpa [S₃, S₂, S₁] using hfresh 104 (by simp))
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 99 (List.replicate r tick) }
  have he₄' : Exec body (usub 98 99 104) (mk v₃ S₃) (4 * (i + 1) + 4) (mk v₄ S₄) := by
    simpa [S₄, S₃, S₂, r, Nat.sub_sub] using he₄
  obtain ⟨v₅, m₅, hu₅, hm₅, he₅⟩ := unaryProduct_exec (body := body)
    (show [(99 : Fin 117), 94, 100, 104, 105].Nodup by decide) v₄ S₄
    (by simpa [S₄, S₃, S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₄, S₃, S₂, S₁] using hfresh 105 (by simp))
  let S₅ : Stacks 117 A := { S₄ with R := Function.update S₄.R 100 (List.replicate (r * W) tick) }
  have he₅' : Exec body (unaryProduct 99 94 100 104 105) (mk v₄ S₄) m₅ (mk v₅ S₅) := by
    simpa [S₅, S₄, S₃, S₂, S₁, hW, hfresh 100 (by simp)] using he₅
  obtain ⟨v₆, m₆, hu₆, hm₆, he₆⟩ := constructFactorRow_exec (body := body) P s t u band L W i hi v₅ S₅ tail
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hW) (by simp [S₅, S₄, S₃, S₂]) (by simp [S₅, r])
    (by simpa [S₅, S₄, S₃, S₂, S₁] using hsrc) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        simpa [S₅, S₄, S₃, S₂, S₁] using hfresh _ (by simp))
  let S₆ : Stacks 117 A := { S₅ with R := Function.update S₅.R 109 (cstream A W (rowFactorWords P s t u band L i) ++ S₅.R 109) }
  obtain ⟨v₇, hu₇, he₇⟩ := clearWords_exec (body := body) [98, 99, 100] (by decide) v₆ S₆
  let S₇ : Stacks 117 A := { S₆ with R := fun k => if k ∈ [(98 : Fin 117), 99, 100] then [] else S₆.R k }
  have he₈ := Exec.act (body := body) (pushN 97 (fun _ => tick) 1 .done) (mk v₇ S₇)
  rw [pushN_run] at he₈
  simp only [Action.run] at he₈
  have hsum : ([(98 : Fin 117), 99, 100].map (fun k => (S₆.R k).length)).sum = L + r * W := by
    simp [S₆, S₅, S₄, S₃, S₂]
    dsimp [r]; omega
  have h99 : (S₄.R 99).length = r := by simp [S₄]
  have h94 : (S₄.R 94).length = W := by simp [S₄, S₃, S₂, S₁, hW]
  rw [h99, h94] at hm₅
  refine ⟨v₇, (4 * i + 4) + (1 + ((4 * L + 4) + ((4 * (i + 1) + 4) +
    (m₅ + (m₆ + ((2 * (L + r * W) + 7) + 1)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans hu₁)))), ?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅' (Exec.seq he₆ (Exec.seq he₇ he₈))))))).cast ?_ ?_⟩
  · unfold factorRowStepCost
    have hrL : r ≤ L := by dsimp [r]; omega
    nlinarith only [hm₅, hm₆, hi, hrL]
  · rw [hsum]; rfl
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h98 : k = 98
    · subst k; simp [S₇, hfresh 98 (by simp)]
    by_cases h99 : k = 99
    · subst k; simp [S₇, hfresh 99 (by simp)]
    by_cases h100 : k = 100
    · subst k; simp [S₇, hfresh 100 (by simp)]
    simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, h98, h99, h100, Function.update_apply] <;>
      split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
