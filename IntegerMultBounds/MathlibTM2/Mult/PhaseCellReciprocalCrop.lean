module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicSlice
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # Publish a reciprocal quotient at the runtime width -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def cropReciprocal : Pr P₀ 117 Q A U :=
  .seq (umul 2 112 98 104)
    (.seq (.act (pushN 98 (fun _ => tick) 8 .done))
      (.seq (takePrefix 98 115 96 104 105) (.seq (uclear 115) (uclear 98))))

theorem cropReciprocal_exec (q W : ℕ) (hw : 2 * q + 8 ≤ W) (z : GaussianInt)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hq : (S.R 112).length = q) (hsrc : S.R 115 = csyms A W z)
    (hfresh : ∀ k ∈ [(98 : Fin 117), 104, 105], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body cropReciprocal (mk v S) (2 * W + 6 * (2 * q + 8) + 4 * q + 15)
        (mk v' { S with R := (Function.update (Function.update S.R 115 []) 96
          (csyms A (2 * q + 8) z ++ S.R 96)) }) := by
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
  have htake : (csyms A W z).take w = csyms A w z := by
    simpa using csyms_floor_div_slice A W 0 w (by simpa using hw) z
  obtain ⟨v₃, hu₃, he₃⟩ := takePrefix_exec (body := body)
    (show [(98 : Fin 117), 115, 96, 104, 105].Nodup by decide) v₁ S₂
    (csyms A w z) ((csyms A W z).drop w)
    (by simp [S₂, S₁, hsrc, ← htake]) (by simp [S₂])
    (by simpa [S₂, S₁] using hfresh 104 (by simp))
    (by simpa [S₂, S₁] using hfresh 105 (by simp))
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update S₂.R 115
    ((csyms A W z).drop w)) 96 (csyms A w z ++ S₂.R 96)) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body 115 v₃ S₃
  let S₄ : Stacks 117 A := { S₃ with R := Function.update S₃.R 115 [] }
  obtain ⟨v₅, hu₅, he₅⟩ := uclear_exec body 98 v₄ S₄
  have hrest : (S₃.R 115).length = W - w := by simp [S₃]
  have hcount : (S₄.R 98).length = w := by simp [S₄, S₃, S₂]
  refine ⟨v₅, hu₅.trans (hu₄.trans (hu₃.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · rw [hrest, hcount]; simp only [csyms, Layer.coeffSyms, List.length_ofFn]; dsimp [w]; omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ho : k = 96
    · subst k; simp [S₄, S₃, S₂, S₁, w]
    by_cases hs : k = 115
    · subst k; simp [S₄]
    by_cases hc : k = 98
    · subst k; simp [hfresh 98 (by simp)]
    simp [S₄, S₃, S₂, S₁, ho, hs, hc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
