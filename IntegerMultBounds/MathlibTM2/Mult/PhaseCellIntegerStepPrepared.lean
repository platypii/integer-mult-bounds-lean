module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIterationRhs

/-! # A generator step that reuses installed arithmetic readiness

The scaled RHS and its exponent are generated and released on every call.
The readiness bank is retained unchanged, so a sequence of iterations pays
for its preparation once.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def preparedIntegerStep (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (generateIterationRhs 102 94 114 116 112 115 107 99 104 106 105) (integerRows hQ)

theorem preparedIntegerStep_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hcount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hiteration : (S.R 116).length = n) (hsaved : S.R 108 = [])
    (hx : S.R 110 = cstream A w (rowColumnWords P s t u band L n) ++ tailX)
    (ha : S.R 111 = cstream A w ((generatorRowJobs P s t u band L n).flatMap Prod.fst) ++ tailA)
    (hc : CClean mul S) (hready : Ready (fun r => S.R (cr r)) w 0)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) (hrest : S.R 107 = []) (hexponent : S.R 115 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ L * (integerRowCost L w + 10 * w + 20) + 21 * w + 53 ∧
      Exec body (preparedIntegerStep hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 111 tailA) 113
          (cstream A w (rowColumnWords P s t u band L (n + 1)) ++ S.R 113)) }) ∧
      ∀ i < L, Fits w (⟨(columnNumerators P s t u band L (n + 1)).getD i 0, 0⟩ : GaussianInt) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateIterationRhs_exec (body := body)
    (show [(102 : Fin 117), 94, 114, 116, 112, 115, 107, 99, 104, 106, 105].Nodup by decide)
    L w P n (by omega) v S hL hwR hprecision hiteration hexponent hrest
    (hwork 99 (by simp [integerRowWork])) (hwork 104 (by simp [integerRowWork]))
    (hwork 106 (by simp [integerRowWork])) (hwork 105 (by simp [integerRowWork]))
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
  have hready₁ : Ready (fun r => S₁.R (cr r)) w 0 := by
    have hrho : (fun r => S₁.R (cr r)) = fun r => S.R (cr r) := by
      funext r
      have hr : cr r ≠ 112 := by
        have hh := (cr_range r).2.1
        intro he
        have hv := congrArg Fin.val he
        omega
      simp [S₁, hr]
    rw [hrho]
    exact hready
  have hwork₁ : ∀ k ∈ integerRowWork, S₁.R k = [] := by
    intro k hk
    have hd : integerRowWork.Disjoint [(112 : Fin 117)] := by
      simp [integerRowWork, cr, OutputPlacement.code]
    have hne : k ≠ 112 := by
      intro he
      subst k
      exact List.disjoint_left.mp hd hk (by simp)
    simpa [S₁, hne] using hwork k hk
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hfits⟩ := integerGeneratorStep_exec (body := body)
    hQ hA hW hP hs hst hu hn v₁ S₁ tailX tailA (S.R 112)
    (by simpa [S₁] using hL) (by simpa [S₁] using hwR)
    (by simpa [S₁] using hcount) (by simpa [S₁] using hsaved)
    (by simpa [S₁] using hx) (by simpa [S₁] using ha)
    (by simp [S₁, generatorRowJobs_rhs]) hclean₁ hready₁ hwork₁
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_, hfits⟩
  · nlinarith only [hm₁, hm₂, hW]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ho : k = 113
    · subst k; simp [S₁]
    by_cases ha' : k = 111
    · subst k; simp
    by_cases hr : k = 112
    · subst k; simp [S₁]
    simp [S₁, ho, ha', hr]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
