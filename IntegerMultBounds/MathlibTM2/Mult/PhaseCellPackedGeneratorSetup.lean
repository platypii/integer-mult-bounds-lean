module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorSetupAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackGenerators

/-! # Construct the retained runtime generator page from the factor page -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generatorPage (A P s t u band L q n : ℕ) : List (Fin (A + 4)) :=
  cstream A (2 * q + 8) (columnWords P s t u band L q n) ++
    (cstream A (2 * q + 8) (reversedColumnWords P s t u band L q n) ++
      csyms A (2 * q + 8) (reciprocalWord P s t u band L q n))

def packedGeneratorBank {A : ℕ} (S : Stacks 117 A) (P s t u band L q W n : ℕ) : Stacks 117 A :=
  { S with R := (Function.update (Function.update (counterR 0 W S.R) 110
    (generatorPage A P s t u band L q n ++ S.R 110)) 116 (List.replicate n tick)) }

noncomputable def generatePackedGenerators (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (generateGenerators hQ) packGenerators

/-- Raw integer words and temporary output tapes are absent from the resulting
page. The original payload beneath tape 110 is retained exactly. -/
theorem generatePackedGenerators_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q W M : ℕ} (hW : P * (M + 2) + 3 ≤ W) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (hqr : q ≤ P * (M + 1) + 1)
    (hwidth : P * (M + 1) + 1 - q + (2 * q + 8) ≤ W)
    (hd : q + P * (M + 1) < W) (hw : 2 * q + 8 ≤ W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailF : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hwR : (S.R 94).length = W)
    (hrowCount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hq : (S.R 112).length = q)
    (hsavedRows : S.R 108 = []) (hcount : (S.R 101).length = M) (hsaved : S.R 100 = [])
    (hfactor : S.R 109 = cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 113, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatorSetupCost P M L q W + packGeneratorsCost L W q ∧
      Exec body (generatePackedGenerators hQ) (mk v S) m
        (mk v' (packedGeneratorBank S P s t u band L q W (M + 1))) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateGenerators_exec (body := body) (band := band)
    hQ hA hW hP hs hst hu hL hqr hwidth hd hw v S tailF hrows hwR hrowCount
    hprecision hq hsavedRows hcount hsaved hfactor hc hblank hfresh
  let S₁ := generatorBank S P s t u band L q W (M + 1)
  have hsmall (k : Fin 117) (hk : k ∈ [(94 : Fin 117), 98, 99, 102, 104, 105, 112]) :
      S₁.R k = S.R k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S₁, generatorBank, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := packGenerators_exec (body := body) L W q
    (rowColumnWords P s t u band L (M + 1)) (columnWords P s t u band L q (M + 1))
    (reversedColumnWords P s t u band L q (M + 1)) (reciprocalWord P s t u band L q (M + 1))
    (by simp [rowColumnWords]) (by simp) (by simp) v₁ S₁ (S.R 110) (S.R 111) (S.R 113)
    (by rw [hsmall 102 (by simp)]; exact hrows)
    (by rw [hsmall 94 (by simp)]; exact hwR) (by rw [hsmall 112 (by simp)]; exact hq)
    (by simp [S₁, generatorBank, encodedColumnBank, generatedColumn])
    (by simp [S₁, generatorBank, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code])
    (by simp [S₁, generatorBank, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code])
    (by simp [S₁, generatorBank])
    (by
      intro k hk
      rw [hsmall k (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        tauto)]
      exact hfresh k ((by decide : [(98 : Fin 117), 99, 104, 105].Sublist
        [96, 97, 98, 99, 104, 105, 106, 107, 113, 115, 116]).subset hk))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, (Exec.seq he₁ he₂).cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases h96 : k = 96
  · subst k; simp [packedGeneratorBank, counterR, cr, OutputPlacement.code, hfresh 96 (by simp)]
  by_cases h110 : k = 110
  · subst k
    simp [packedGeneratorBank, generatorPage, List.append_assoc]
  by_cases h111 : k = 111
  · subst k; simp [packedGeneratorBank, counterR, cr, OutputPlacement.code]
  by_cases h113 : k = 113
  · subst k; simp [packedGeneratorBank, counterR, cr, OutputPlacement.code]
  simp [S₁, generatorBank, encodedColumnBank, generatedColumn, packedGeneratorBank, h96, h110, h111, h113, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
