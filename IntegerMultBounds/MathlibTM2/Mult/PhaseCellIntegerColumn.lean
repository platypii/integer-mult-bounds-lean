module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerColumnSeed
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIterationsSetup

/-! # Construct the integer inverse column from a retained factor page

The program initializes the actual unit seed and iteration header, prepares
readiness once, and executes every requested iteration. Factor-page generation
and final quotient/reciprocal encoding are separate setup obligations.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def generateIntegerColumn (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq initializeIntegerColumn (prepareIntegerIterations hQ)

def generatedColumn {A : ℕ} (S : Stacks 117 A) (w : ℕ) (xs : List GaussianInt) (n : ℕ) : Stacks 117 A :=
  { S with R := (Function.update (Function.update (counterR 0 w S.R) 110
    (cstream A w xs ++ S.R 110)) 116 (List.replicate n tick)) }

/-- The full integer recurrence executes from the supplied factor page and
ordinary headers; no input column, RHS page or arithmetic readiness is supplied. -/
theorem generateIntegerColumn_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L w M : ℕ} (hW : P * (M + 2) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailF : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hrowCount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hsavedRows : S.R 108 = []) (hcount : (S.R 101).length = M) (hsaved : S.R 100 = [])
    (hfactor : S.R 109 = cstream A w ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ prepareCost 0 w + M * (integerIterationCost L w + 5) + 10 * (L * w) + 9 * L + 6 * P + 22 ∧
      Exec body (generateIntegerColumn hQ) (mk v S) m
        (mk v' (generatedColumn S w (rowColumnWords P s t u band L (M + 1)) (M + 1))) ∧
      IntegerGeneratorContext P s t u band L (M + 1) w (S.R 110) tailF
        (generatedColumn S w (rowColumnWords P s t u band L (M + 1)) (M + 1)) := by
  have hPW : P < w := by nlinarith
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := initializeIntegerColumn_exec (body := body) P s t u band L w hL hPW
    v S hrows hwR hprecision (hfresh 116 (by simp))
    (fun k hk => hfresh k ((by decide : [(99 : Fin 117), 104, 105, 106].Sublist
      [96, 97, 98, 99, 104, 105, 106, 107, 115, 116]).subset hk))
  let SI := initializedColumn S w (rowColumnWords P s t u band L 1)
  have hsmall (k : Fin 117) (hk : k.val < 96) : SI.R k = S.R k := by
    have h110 : k ≠ 110 := by intro he; have hv := congrArg Fin.val he; omega
    have h116 : k ≠ 116 := by intro he; have hv := congrArg Fin.val he; omega
    simp [SI, initializedColumn, h110, h116]
  have hcleanI : CClean mul SI := by
    intro i
    refine ⟨(hc i).1, ?_⟩
    rw [hsmall (mul i) (by have hi := i.isLt; simp [mul]; omega)]
    exact (hc i).2
  have hblankI : ∀ r, SI.R (cr r) = [] := by
    intro r
    rw [hsmall (cr r) (by have hr := (cr_range r).2.1; omega)]
    exact hblank r
  have hfreshI : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115], SI.R k = [] := by
    intro k hk
    have hoff : k ≠ 110 ∧ k ≠ 116 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hk' := (by decide : [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115].Sublist
      [96, 97, 98, 99, 104, 105, 106, 107, 115, 116]).subset hk
    simpa [SI, initializedColumn, hoff.1, hoff.2] using hfresh k hk'
  have hW' : P * (1 + M + 1) + 3 ≤ w := by
    have heq : 1 + M + 1 = M + 2 := by omega
    simpa only [heq] using hW
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hctx₂⟩ := prepareIntegerIterations_exec (body := body) (n := 1) (M := M) (band := band)
    hQ hA hW' hP hs hst hu (by decide) v₁ SI (S.R 110) tailF
    (by simpa [SI, initializedColumn] using hrows) (by simpa [SI, initializedColumn] using hwR)
    (by simpa [SI, initializedColumn] using hrowCount) (by simpa [SI, initializedColumn] using hprecision)
    (by simp [SI, initializedColumn]) (by simpa [SI, initializedColumn] using hsavedRows)
    (by simpa [SI, initializedColumn] using hcount) (by simpa [SI, initializedColumn] using hsaved)
    (by simp [SI, initializedColumn]) (by simpa [SI, initializedColumn] using hfactor) hcleanI hblankI hfreshI
  have hidx : 1 + M = M + 1 := by omega
  rw [hidx] at he₂ hctx₂
  have hstate : iteratedColumns { SI with R := counterR 0 w SI.R } w
      (rowColumnWords P s t u band L (M + 1)) (S.R 110) M =
      generatedColumn S w (rowColumnWords P s t u band L (M + 1)) (M + 1) := by
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hi : k = 116
    · subst k
      simp [iteratedColumns, generatedColumn, SI, initializedColumn, counterR, cr, OutputPlacement.code,
        List.replicate_succ']
    by_cases hx : k = 110
    · subst k; simp [iteratedColumns, generatedColumn]
    simp [iteratedColumns, generatedColumn, SI, initializedColumn, counterR, Function.update_apply, hi, hx]
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl (congrArg (mk v₂) hstate), hstate ▸ hctx₂⟩
  nlinarith only [hm₁, hm₂]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
