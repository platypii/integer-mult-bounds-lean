module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightRoute
public import IntegerMultBounds.MathlibTM2.Mult.ChirpScaleExec

/-! # Execute output rescaling above an arbitrary persistent suffix

Counted routing isolates the owned prefix before the existing exact shift
machine runs. Every generated count and staging port is restored on return.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.ChirpSt IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Layer

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def scaleOutputPrefix : Pr P 117 Q A U :=
  .seq (branchWords 108 3 2 103 1 7 8)
    (.seq (takeFromWords 1 94 2 93 84 7 8) (.seq (uclear 1)
      (.seq (shiftInto 84 26 84 116 115 27 28 (pairSym A false false))
        (.seq (moveR 84 26 id) (moveR 26 93 id)))))

def scaleOutputPrefixCost (M L w d : ℕ) : ℕ :=
  (M * L) * (22 * w + 4 * d + 29) + 17 * M + 32

theorem scaleOutputPrefix_exec (M L w d : ℕ) (hw : 1 ≤ w) (hd : d ≤ w) (xs : List GaussianInt)
    (hlen : xs.length = M * L) (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hwidth : (S.R 94).length = w) (hshift : (S.R 116).length = d) (hrest : (S.R 115).length = w - d)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 7, 8, 26, 27, 28, 84], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ scaleOutputPrefixCost M L w d ∧
      Exec body scaleOutputPrefix (mk v S) m
        (mk v' { S with R := (Function.update S.R 93
          (cstream A w (xs.map (fun x => (2 : GaussianInt) ^ d * x)) ++ tail)) }) := by
  have hxs : (cstream A w xs).length = M * L * w := by simp [hlen]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := branchWords_exec (body := body)
    (batch := 108) (saved := 3) (half := 2) (rows := 103) (words := 1) (buf := 7) (tmp := 8)
    (by decide) M L v S (by omega) hrows (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hclean _ (by simp))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 1 (List.replicate (M * L) tick) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := takeFromWords_exec (body := body)
    (words := 1) (width := 94) (count := 2) (src := 93) (dst := 84) (buf := 7) (tmp := 8)
    (by decide) (M * L) w v₁ S₁ (cstream A w xs) tail
    (by simp [S₁]) (by simpa [S₁] using hwidth) hxs (by simpa [S₁] using hsrc)
    (by simp [S₁, hclean 2 (by simp)]) (by simp [S₁, hclean 7 (by simp)])
    (by simp [S₁, hclean 8 (by simp)])
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update S₁.R 93 tail) 84 (cstream A w xs)) }
  have he₂' : Exec body (takeFromWords 1 94 2 93 84 7 8) (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    simpa only [S₁, Function.update_of_ne (show (84 : Fin 117) ≠ 1 by decide),
      hclean 84 (by simp), List.append_nil] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := uclear_exec body 1 v₂ S₂
  let S₃ : Stacks 117 A := { S₂ with R := Function.update S₂.R 1 [] }
  obtain ⟨v₄, hu₄, he₄⟩ := chirpScale_exec (body := body)
    (src := 84) (buf := 26) (shift := 116) (rest := 115) (savedShift := 27) (savedRest := 28)
    (by decide) w d hw hd xs v₃ S₃ (by simp [S₃, S₂])
    (by simpa [S₃, S₂, S₁] using hshift) (by simpa [S₃, S₂, S₁] using hrest)
    (by simp [S₃, S₂, S₁, hclean 26 (by simp)])
    (by simp [S₃, S₂, S₁, hclean 27 (by simp)])
    (by simp [S₃, S₂, S₁, hclean 28 (by simp)])
  let shifted := xs.map (fun x => (2 : GaussianInt) ^ d * x)
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 84 (cstream A w shifted) }
  obtain ⟨v₅, hu₅, he₅⟩ := moveR_exec body 84 26 (by decide) id v₄ S₄
  let S₅ : Stacks 117 A := { S₄ with R := movedR S₄.R 84 26 id (S₄.R 84) }
  obtain ⟨v₆, hu₆, he₆⟩ := moveR_exec body 26 93 (by decide) id v₅ S₅
  have hc : (S₂.R 1).length = M * L := by simp [S₂, S₁]
  have hm₄ : (S₄.R 84).length = M * L * w := by simp [S₄, shifted, hlen]
  have hm₅ : (S₅.R 26).length = M * L * w := by
    simp [S₅, S₄, S₃, S₂, S₁, movedR, shifted, hlen, hclean 26 (by simp)]
  refine ⟨v₆, m₁ + (m₂ + ((2 * (M * L) + 2) +
    ((xs.length * (6 * w + 4 * d + 14) + 4) + ((2 * (M * L * w) + 2) + (2 * (M * L * w) + 2))))),
    hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))), ?_, ?_⟩
  · unfold scaleOutputPrefixCost
    rw [hlen]
    nlinarith only [hm₁, hm₂]
  · refine (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))).cast
      (by rw [hc, hm₄, hm₅]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    clear he₁ he₂ he₂' he₃ he₄ he₅ he₆ hu₁ hu₂ hu₃ hu₄ hu₅ hu₆
    funext k
    by_cases hk93 : k = (93 : Fin 117)
    · subst k
      simp [S₅, S₄, S₃, S₂, S₁, movedR, shifted, hclean 26 (by simp)]
    · by_cases hk84 : k = (84 : Fin 117)
      · subst k
        simp [S₅, S₄, S₃, S₂, S₁, movedR, hclean 84 (by simp)]
      · by_cases hk26 : k = (26 : Fin 117)
        · subst k
          simp [S₅, S₄, S₃, S₂, S₁, movedR, hclean 26 (by simp)]
        · by_cases hk1 : k = (1 : Fin 117)
          · subst k; simp [S₅, S₄, S₃, S₂, S₁, movedR, hclean 1 (by simp)]
          · simp [S₅, S₄, S₃, S₂, S₁, movedR, Function.update_apply, hk93, hk84, hk26, hk1]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
