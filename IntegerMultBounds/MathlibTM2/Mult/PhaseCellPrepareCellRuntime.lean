module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseConstruction
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCellHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSwapCellPayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorPage

/-! Execute the transition from constructed numerical setup to runtime headers
and the per-call payload layout, retaining the generated numerical page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareCellRuntime : Pr P₀ 117 Q A U :=
  .seq releaseConstruction (.seq installCellHeaders swapCellPayload)

def prepareCellRuntimeCost (P M L q l W : ℕ) : ℕ :=
  releaseConstructionCost L W (M + 1) + installCellHeadersCost P M q l + swapCellPayloadCost L (2 * q + 8)

theorem prepareCellRuntime_exec (P s t u band L q l W M : ℕ)
    (outs factors rhs tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hM : (S.R 101).length = M)
    (hq : (S.R 112).length = q) (hl : (S.R 109).length = l)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L) (hwidth : (S.R 94).length = W)
    (houts : outs.length = L * (2 * q + 8)) (hfactors : factors.length = L * (2 * q + 8))
    (hrhs : rhs.length = L * (2 * q + 8)) (hsrc : S.R 110 = outs ++ (factors ++ (rhs ++ tail)))
    (hblank : ∀ r, S.R (cr r) = []) (hiteration : S.R 116 = [])
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 100, 104, 105, 106, 107, 108], S.R k = []) :
    let B := cellHeaderBank (retainedGeneratorBank S P s t u band L q (M + 1)) q l
    let pre := generatorPage A P s t u band L q (M + 1) ++ outs
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCellRuntimeCost P M L q l W ∧
      Exec body prepareCellRuntime
        (mk v (packedGeneratorBank (constructedFactorBank S P s t u band L W)
          P s t u band L q W (M + 1))) m
        (mk v' { B with R := Function.update B.R 110 (pre ++ (rhs ++ (factors ++ tail))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := releaseConstruction_exec (body := body)
    P s t u band L q W (M + 1) v S hrows hcount hwidth hblank hiteration (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let T := retainedGeneratorBank S P s t u band L q (M + 1)
  obtain ⟨v₂, hu₂, he₂⟩ := installCellHeaders_exec (body := body) P M q l v₁ T
    (by simpa [T, retainedGeneratorBank] using hP) (by simpa [T, retainedGeneratorBank] using hM)
    (by simpa [T, retainedGeneratorBank] using hq) (by simpa [T, retainedGeneratorBank] using hl) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · simp [T, retainedGeneratorBank]
      · simpa [T, retainedGeneratorBank] using hfresh 100 (by simp)
      · simpa [T, retainedGeneratorBank] using hfresh 104 (by simp)
      · simpa [T, retainedGeneratorBank] using hfresh 108 (by simp))
  let B := cellHeaderBank T q l
  let pre := generatorPage A P s t u band L q (M + 1) ++ outs
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := swapCellPayload_exec (body := body) L (2 * q + 8)
    pre factors rhs tail v₂ B
    (by simpa [B, cellHeaderBank, T, retainedGeneratorBank] using hrows)
    (by simp [B, cellHeaderBank])
    (by simp [pre, houts]; ring) hfactors hrhs
    (by simp [B, cellHeaderBank, T, retainedGeneratorBank, hsrc, pre, List.append_assoc]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simpa [B, cellHeaderBank, T, retainedGeneratorBank] using hfresh _ (by simp))
  exact ⟨v₃, m₁ + (installCellHeadersCost P M q l + m₃), hu₃.trans (hu₂.trans hu₁),
    by unfold prepareCellRuntimeCost; omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
