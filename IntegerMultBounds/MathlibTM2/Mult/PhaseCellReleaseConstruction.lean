module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseFactorPage

/-! Release construction-only storage while retaining the complete runtime page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseConstruction : Pr P₀ 117 Q A U :=
  .seq releaseFactorPage (clearWords [cr .wn, cr .pn, cr .nn, 116, 94])

def releaseConstructionCost (L W n : ℕ) : ℕ :=
  releaseFactorPageCost L W + 2 * (2 * W + Schoenhage.Schedule.topN W + n) + 11

def retainedGeneratorBank {A : ℕ} (S : Stacks 117 A) (P s t u band L q n : ℕ) : Stacks 117 A :=
  { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
    generatorPage A P s t u band L q n ++ S.R 110 else if k = 94 then [] else S.R k) }

theorem releaseConstruction_exec (P s t u band L q W n : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hcount : (S.R 103).length = L) (hwidth : (S.R 94).length = W)
    (hblank : ∀ r, S.R (cr r) = []) (hiteration : S.R 116 = [])
    (hfresh : ∀ k ∈ [(97 : Fin 117), 99, 104, 105, 106], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseConstructionCost L W n ∧
      Exec body releaseConstruction
        (mk v (packedGeneratorBank (constructedFactorBank S P s t u band L W) P s t u band L q W n)) m
        (mk v' (retainedGeneratorBank S P s t u band L q n)) := by
  let B := packedGeneratorBank (constructedFactorBank S P s t u band L W) P s t u band L q W n
  have hlen : (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L))).length = L * L * W := by
    simp [List.length_flatMap, rowFactorWords]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := releaseFactorPage_exec (body := body) L W
    (cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L))) (S.R 109) v B
    (by simpa [B, packedGeneratorBank, constructedFactorBank, counterR, cr, OutputPlacement.code] using hrows)
    (by simpa [B, packedGeneratorBank, constructedFactorBank, counterR, cr, OutputPlacement.code] using hcount)
    (by simpa [B, packedGeneratorBank, constructedFactorBank, counterR, cr, OutputPlacement.code] using hwidth)
    hlen (by simp [B, packedGeneratorBank, constructedFactorBank, counterR, cr, OutputPlacement.code]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simpa [B, packedGeneratorBank, constructedFactorBank, counterR, cr, OutputPlacement.code] using hfresh _ (by simp))
  let C : Stacks 117 A := { B with R := Function.update B.R 109 (S.R 109) }
  obtain ⟨v₂, hu₂, he₂⟩ := clearWords_exec (body := body) [cr .wn, cr .pn, cr .nn, 116, 94]
    (by decide) v₁ C
  have hsum : ([cr .wn, cr .pn, cr .nn, (116 : Fin 117), 94].map (fun k => (C.R k).length)).sum =
      2 * W + Schoenhage.Schedule.topN W + n := by
    simp [C, B, packedGeneratorBank, constructedFactorBank, counterR, cr, OutputPlacement.code, hwidth]
    omega
  refine ⟨v₂, m₁ + (2 * (2 * W + Schoenhage.Schedule.topN W + n) + 11), hu₂.trans hu₁,
    by unfold releaseConstructionCost; omega, (Exec.seq he₁ he₂).cast (by rw [hsum]; rfl) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h116 : k = 116
    · subst k; simp [retainedGeneratorBank, hiteration]
    by_cases hwn : k = cr .wn
    · subst k
      simp [retainedGeneratorBank, cr, OutputPlacement.code]
      simpa [cr, OutputPlacement.code] using hblank .wn
    by_cases hpn : k = cr .pn
    · subst k
      simp [retainedGeneratorBank, cr, OutputPlacement.code]
      simpa [cr, OutputPlacement.code] using hblank .pn
    by_cases hnn : k = cr .nn
    · subst k
      simp [retainedGeneratorBank, cr, OutputPlacement.code]
      simpa [cr, OutputPlacement.code] using hblank .nn
    by_cases h94 : k = 94
    · subst k; simp [retainedGeneratorBank]
    simp [C, B, retainedGeneratorBank, packedGeneratorBank, constructedFactorBank, counterR,
      h116, hwn, hpn, hnn, h94, Function.update_apply]
    by_cases hk109 : k = 109
    · subst k; simp
    by_cases hk110 : k = 110
    · subst k; simp
    by_cases hklo : k.val < 63 <;> simp [hk109, hk110, hklo]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
