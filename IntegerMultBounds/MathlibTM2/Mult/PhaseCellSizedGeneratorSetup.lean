module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeneratorAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupWidth

/-! # Generate, pack and release the inverse setup with its own word-width header -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def setupWidthBank {A : ℕ} (S : Stacks 117 A) (P q M : ℕ) : Stacks 117 A :=
  { S with R := Function.update S.R 94 (List.replicate (integerSetupWidth P q (M + 1) 0) tick) }

noncomputable def sizedGeneratorSetup (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq generateSetupWidth (generatePackedGenerators hQ)

def sizedGeneratorRelease : Pr P₀ 117 Q A U := .seq releasePackedSetup (uclear 94)

/-- The setup width is generated and every arithmetic width condition is derived.
Only ordinary P/M/q/L headers and the retained factor page are supplied. -/
theorem sizedGeneratorSetup_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q M : ℕ} (hP : 13 ≤ P) (hqMax : q ≤ 2 * (M + 1))
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailF : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hrowCount : (S.R 103).length = L)
    (hprecision : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hsavedRows : S.R 108 = []) (hcount : (S.R 101).length = M) (hsaved : S.R 100 = [])
    (hfactor : S.R 109 = cstream A (integerSetupWidth P q (M + 1) 0)
      ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 97, 98, 99, 104, 105, 106, 107, 113, 115, 116], S.R k = []) :
    let W := integerSetupWidth P q (M + 1) 0
    ∃ v' m, v'.user = v.user ∧
      m ≤ 4 * (P * M) + 13 * P + 4 * q + 13 + generatorSetupCost P M L q W + packGeneratorsCost L W q ∧
      Exec body (sizedGeneratorSetup hQ) (mk v S) m
        (mk v' (packedGeneratorBank (setupWidthBank S P q M) P s t u band L q W (M + 1))) := by
  let W := integerSetupWidth P q (M + 1) 0
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateSetupWidth_exec (body := body) P M q v S hprecision hcount hq
    (fun k hk => hfresh k ((by decide : [(94 : Fin 117), 104, 105].Sublist
      [94, 96, 97, 98, 99, 104, 105, 106, 107, 113, 115, 116]).subset hk))
  let S₁ := setupWidthBank S P q M
  have hclean : CClean mul S₁ := by
    intro i
    refine ⟨(hc i).1, ?_⟩
    have hoff : mul i ≠ (94 : Fin 117) := by
      intro he
      have hv := congrArg Fin.val he
      have hi := i.isLt
      simp only [mul] at hv
      omega
    simpa [S₁, setupWidthBank, hoff] using (hc i).2
  have hblank₁ : ∀ r, S₁.R (cr r) = [] := by
    intro r
    have hoff : cr r ≠ (94 : Fin 117) := by
      intro he; exact (cr_range r).2.2.2 (congrArg Fin.val he)
    simpa [S₁, setupWidthBank, hoff] using hblank r
  have hfresh₁ : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 113, 115, 116], S₁.R k = [] := by
    intro k hk
    have hoff : k ≠ 94 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁, setupWidthBank, hoff] using hfresh k (List.mem_cons_of_mem 94 hk)
  obtain ⟨hW, hqr, hwidth, hd, hw⟩ := integerSetupWidth_generator hP hqMax
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := generatePackedGenerators_exec (body := body) (band := band)
    hQ hA hW hP hs hst hu hL hqr hwidth hd hw v₁ S₁ tailF
    (by simpa [S₁, setupWidthBank] using hrows) (by simp [S₁, setupWidthBank])
    (by simpa [S₁, setupWidthBank] using hrowCount) (by simpa [S₁, setupWidthBank] using hprecision)
    (by simpa [S₁, setupWidthBank] using hq) (by simpa [S₁, setupWidthBank] using hsavedRows)
    (by simpa [S₁, setupWidthBank] using hcount) (by simpa [S₁, setupWidthBank] using hsaved)
    (by simpa [S₁, setupWidthBank] using hfactor) hclean hblank₁ hfresh₁
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

/-- Releasing this setup also releases its generated width header. -/
theorem sizedGeneratorRelease_exec (P s t u band L q M : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hrows : (S.R 102).length = L) (hq : (S.R 112).length = q)
    (hblank : ∀ r, S.R (cr r) = []) (hiteration : S.R 116 = []) (hwidth : S.R 94 = [])
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105], S.R k = []) :
    let W := integerSetupWidth P q (M + 1) 0
    ∃ v' m, v'.user = v.user ∧ m ≤ releasePackedSetupCost L q W (M + 1) + 2 * W + 2 ∧
      Exec body sizedGeneratorRelease
        (mk v (packedGeneratorBank (setupWidthBank S P q M) P s t u band L q W (M + 1))) m (mk v' S) := by
  let W := integerSetupWidth P q (M + 1) 0
  let S₁ := setupWidthBank S P q M
  have hblank₁ : ∀ r, S₁.R (cr r) = [] := by
    intro r
    have hoff : cr r ≠ (94 : Fin 117) := by
      intro he; exact (cr_range r).2.2.2 (congrArg Fin.val he)
    simpa [S₁, setupWidthBank, hoff] using hblank r
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := releasePackedSetup_exec (body := body)
    P s t u band L q W (M + 1) v S₁
    (by simpa [S₁, setupWidthBank] using hrows) (by simpa [S₁, setupWidthBank] using hq) hblank₁
    (by simpa [S₁, setupWidthBank] using hiteration) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;>
        simpa [S₁, setupWidthBank] using hfresh _ (by simp))
  obtain ⟨v₂, hu₂, he₂⟩ := uclear_exec body 94 v₁ S₁
  refine ⟨v₂, m₁ + (2 * W + 2), hu₂.trans hu₁, by dsimp [W] at hm₁ ⊢; omega,
    (Exec.seq he₁ he₂).cast (by simp [S₁, setupWidthBank, W]) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases hk : k = 94
  · subst k; simp [hwidth]
  simp [S₁, setupWidthBank, hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
