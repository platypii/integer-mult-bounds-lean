module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseFactorPage

/-! # Release the complete numerically constructed inverse setup

The binary table header bank is owned input and has been consumed. Every other
original stack and borrowed suffix is restored after releasing both pages.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def numericalGeneratorRelease : Pr P₀ 117 Q A U := .seq releasePackedSetup releaseFactorPage

/-- Runtime page, factor page, iteration/readiness counters and all release
workspace are paid; the original bank outside the consumed table headers returns. -/
theorem numericalGeneratorRelease_exec (P s t u band L q W n : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L)
    (hq : (S.R 112).length = q) (hwidth : (S.R 94).length = W)
    (hblank : ∀ r, S.R (cr r) = []) (hiteration : S.R 116 = [])
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releasePackedSetupCost L q W n + releaseFactorPageCost L W ∧
      Exec body numericalGeneratorRelease
        (mk v (packedGeneratorBank (constructedFactorBank S P s t u band L W) P s t u band L q W n)) m
        (mk v' { S with R := fun k => if k.val < 63 then [] else S.R k }) := by
  let S₁ := constructedFactorBank S P s t u band L W
  have hblank₁ : ∀ r, S₁.R (cr r) = [] := by
    intro r
    have hr := cr_range r
    have hlo : ¬ (cr r).val < 63 := by omega
    have h109 : cr r ≠ (109 : Fin 117) := by intro he; have hv := congrArg Fin.val he; omega
    simpa [S₁, constructedFactorBank, hlo, h109] using hblank r
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := releasePackedSetup_exec (body := body)
    P s t u band L q W n v S₁
    (by simpa [S₁, constructedFactorBank] using hrows) (by simpa [S₁, constructedFactorBank] using hq)
    hblank₁ (by simpa [S₁, constructedFactorBank] using hiteration) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₁, constructedFactorBank] using hfresh _ (by simp))
  have hlen : (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L))).length = L * L * W := by
    simp [List.length_flatMap, rowFactorWords]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseFactorPage_exec (body := body) L W
    (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L))) (S.R 109) v₁ S₁
    (by simpa [S₁, constructedFactorBank] using hrows) (by simpa [S₁, constructedFactorBank] using hcount)
    (by simpa [S₁, constructedFactorBank] using hwidth) hlen (by simp [S₁, constructedFactorBank]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₁, constructedFactorBank] using hfresh _ (by simp))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = 109
  · subst k; simp
  simp [S₁, constructedFactorBank, hk, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
