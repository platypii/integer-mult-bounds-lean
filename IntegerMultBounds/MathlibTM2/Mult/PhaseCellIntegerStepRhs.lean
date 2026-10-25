module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStepSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIterationRhs

/-! # Execute a generator iteration with a generated RHS page

Only the factor page is consumed input. The scaled RHS is generated from the
row/width/P/iteration headers and consumed by the row loop, restoring its exact
original suffix. Readiness is generated once and remains installed afterward.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def generateRhsIntegerStep (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (generateIterationRhs 102 94 114 116 112 115 107 99 104 106 105) (prepareIntegerStep hQ)

/-- The RHS page, its exponent and scalar readiness are generated and paid,
including empty interiors. Every generated RHS symbol is consumed before return. -/
theorem generateRhsIntegerStep_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w) (hqR : (S.R 100).length = 0)
    (hcount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hiteration : (S.R 116).length = n) (hsaved : S.R 108 = [])
    (hx : S.R 110 = cstream A w (rowColumnWords P s t u band L n) ++ tailX)
    (ha : S.R 111 = cstream A w ((generatorRowJobs P s t u band L n).flatMap Prod.fst) ++ tailA)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ prepareCost 0 w + L * (integerRowCost L w + 10 * w + 20) + 21 * w + 53 ∧
      Exec body (generateRhsIntegerStep hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (counterR 0 w S.R) 111 tailA) 113
          (cstream A w (rowColumnWords P s t u band L (n + 1)) ++ S.R 113)) }) ∧
      ∀ i < L, Fits w (⟨(columnNumerators P s t u band L (n + 1)).getD i 0, 0⟩ : GaussianInt) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateIterationRhs_exec (body := body)
    (show [(102 : Fin 117), 94, 114, 116, 112, 115, 107, 99, 104, 106, 105].Nodup by decide)
    L w P n (by omega) v S hL hwR hprecision hiteration
    (hfresh 115 (by simp)) (hfresh 107 (by simp)) (hfresh 99 (by simp)) (hfresh 104 (by simp))
    (hfresh 106 (by simp)) (hfresh 105 (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update S.R 112
    (cstream A w ((seedWords (P * (n + 1)) L).reverse) ++ S.R 112)) }
  have hclean₁ : CClean mul S₁ := by
    intro i
    refine ⟨(hc i).1, ?_⟩
    have hi : mul i ≠ 112 := by
      intro he
      have hv := congrArg Fin.val he
      have hil := i.isLt
      simp only [mul] at hv
      omega
    simpa [S₁, hi] using (hc i).2
  have hblank₁ : ∀ r, S₁.R (cr r) = [] := by
    intro r
    have hr : cr r ≠ 112 := by
      have hh := (cr_range r).2.1
      intro he
      have hv := congrArg Fin.val he
      omega
    simpa [S₁, hr] using hblank r
  have hfresh₁ : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106], S₁.R k = [] := by
    intro k hk
    have hne : k ≠ 112 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk' : k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115] :=
      (by decide : [(96 : Fin 117), 97, 98, 99, 104, 105, 106].Sublist
        [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115]).subset hk
    simpa [S₁, hne] using hfresh k hk'
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hfits⟩ := prepareIntegerStep_exec (body := body)
    hQ hA hW hP hs hst hu hn v₁ S₁ tailX tailA (S.R 112)
    (by simpa [S₁] using hL) (by simpa [S₁] using hwR) (by simpa [S₁] using hqR)
    (by simpa [S₁] using hcount) (by simpa [S₁] using hsaved)
    (by simpa [S₁] using hx) (by simpa [S₁] using ha)
    (by simp [S₁, generatorRowJobs_rhs]) hclean₁ hblank₁ hfresh₁
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_, hfits⟩
  · nlinarith only [hm₁, hm₂, hW]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ho : k = 113
    · subst k; simp [S₁, counterR, cr, OutputPlacement.code]
    by_cases ha' : k = 111
    · subst k; simp
    by_cases hr : k = 112
    · subst k; simp [S₁, counterR, cr, OutputPlacement.code]
    simp [S₁, counterR, Function.update_apply, ho, ha', hr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
