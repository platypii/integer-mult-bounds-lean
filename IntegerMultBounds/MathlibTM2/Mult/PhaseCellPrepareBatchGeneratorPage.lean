module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchGeneratorPage

/-! Load the delayed batch control, generate runtime width and expand the one
computed inverse page. The control suffix remains available for runtime setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareBatchGeneratorPage : Pr P₀ 117 Q A U :=
  .seq loadBatchHeader (.seq (umul 2 112 94 104)
    (.seq (.act (pushN 94 (fun _ => tick) 8 .done)) replicateGenerators))

def prepareBatchGeneratorPageCost (B L q : ℕ) : ℕ :=
  (4 * B + 7) + (4 * q + 5) + replicateGeneratorsCost B L (2 * q + 8)

theorem prepareBatchGeneratorPage_exec (B P s t u band L q n : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (controlTail tail : List (Fin (A + 4)))
    (hL : (S.R 103).length = L) (hq : (S.R 112).length = q)
    (hcontrol : S.R 109 = List.replicate B tick ++ blank :: controlTail)
    (hsrc : S.R 110 = generatorPage A P s t u band L q n ++ tail)
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 97, 98, 99, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareBatchGeneratorPageCost B L q ∧
      Exec body prepareBatchGeneratorPage (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update (Function.update S.R
          109 controlTail) 96 (List.replicate B tick)) 94 (List.replicate (2 * q + 8) tick))
          110 (batchGeneratorPage A B P s t u band L q n ++ tail)) }) := by
  let w := 2 * q + 8
  obtain ⟨v₁, hu₁, he₁⟩ := loadBatchHeader_exec (body := body) B controlTail v S hcontrol
    (hfresh 96 (by simp)) (hfresh 107 (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update S.R 109 controlTail) 96 (List.replicate B tick)) }
  obtain ⟨v₂, hu₂, he₂⟩ := umul_exec (body := body) 2 (a := 112) (b := 94) (t := 104)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hfresh 104 (by simp))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 94 (List.replicate (2 * q) tick) }
  have he₂' : Exec body (umul 2 112 94 104) (mk v₁ S₁) (4 * q + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, hq, hfresh 94 (by simp)] using he₂
  let S₃ : Stacks 117 A := { S₁ with R := Function.update S₁.R 94 (List.replicate w tick) }
  have he₃ : Exec body (.act (pushN 94 (fun _ => tick) 8 .done)) (mk v₂ S₂) 1 (mk v₂ S₃) := by
    have he := Exec.act (body := body) (pushN 94 (fun _ => tick) 8 .done) (mk v₂ S₂)
    rw [pushN_run] at he
    simpa only [S₃, S₂, Action.run, Function.update_self, Function.update_idem, List.replicate_append_replicate,
      show 8 + 2 * q = w by dsimp [w]; omega] using he
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := replicateGeneratorPage_exec (body := body) B P s t u band L q n v₂ S₃ tail
    (by simp [S₃, S₁]) (by simpa [S₃, S₁] using hL) (by simp [S₃, w])
    (by simpa [S₃, S₁] using hsrc) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₃, S₁] using hfresh _ (by simp))
  refine ⟨v₄, (4 * B + 7) + ((4 * q + 4) + (1 + m₄)), hu₄.trans (hu₂.trans hu₁),
    by unfold prepareBatchGeneratorPageCost; omega, Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃ he₄))⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
