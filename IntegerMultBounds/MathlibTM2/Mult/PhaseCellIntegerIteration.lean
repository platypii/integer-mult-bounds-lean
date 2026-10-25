module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStepPrepared
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellColumnReplace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorCopy

/-! # A repeatable executed integer generator iteration

Borrow a retained factor page, generate the RHS, run every row, install the
next column and increment the iteration header. All temporary copies and
output prefixes are released; arithmetic readiness is retained unchanged.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def integerIteration (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (copyFactorPage 102 103 94 107 99 109 111 104 105)
    (.seq (preparedIntegerStep hQ) (.seq (replaceColumn 102 94 99 110 113 104 105) (.act (pushOne 116))))

def integerIterationCost (L w : ℕ) : ℕ :=
  16 * (L * L * w) + 15 * (L * L) + L * (integerRowCost L w + 28 * w + 38) + 21 * w + 94

def iteratedColumn {A : ℕ} (S : Stacks 117 A) (w : ℕ) (xs : List GaussianInt)
    (tailX : List (Fin (A + 4))) : Stacks 117 A :=
  { S with R := (Function.update (Function.update S.R 110 (cstream A w xs ++ tailX)) 116 (tick :: S.R 116)) }

/-- One genuine machine iteration preserves the retained factor page, both
publication/RHS suffixes and every work tape, and is ready to run again. -/
theorem integerIteration_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailF : List (Fin (A + 4)))
    (hctx : IntegerRowContext L w (rowColumnWords P s t u band L n) tailX S)
    (hcount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hiteration : (S.R 116).length = n) (hsaved : S.R 108 = [])
    (hfactor : S.R 109 = cstream A w ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hrest : S.R 107 = []) (hexponent : S.R 115 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ integerIterationCost L w ∧
      Exec body (integerIteration hQ) (mk v S) m
        (mk v' (iteratedColumn S w (rowColumnWords P s t u band L (n + 1)) tailX)) ∧
      IntegerRowContext L w (rowColumnWords P s t u band L (n + 1)) tailX
        (iteratedColumn S w (rowColumnWords P s t u band L (n + 1)) tailX) := by
  let factors := cstream A w ((generatorRowJobs P s t u band L n).flatMap Prod.fst)
  have hflen : factors.length = L * L * w := by
    dsimp only [factors]
    rw [length_cstream, generatorRowJobs_factor_length]
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := copyFactorPage_exec (body := body)
    (show [(102 : Fin 117), 103, 94, 107, 99, 109, 111, 104, 105].Nodup by decide)
    L w v S factors tailF hctx.rows hcount hctx.width
    (by simpa only [factors, generatorRowJobs_factors] using hfactor) hflen hrest
    (hctx.work 99 (by simp [integerRowWork])) (hctx.work 104 (by simp [integerRowWork]))
    (hctx.work 105 (by simp [integerRowWork]))
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 111 (factors ++ S.R 111) }
  have hctx₁ : IntegerRowContext L w (rowColumnWords P s t u band L n) tailX S₁ :=
    hctx.update 111 (by simp) (factors ++ S.R 111)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hfits⟩ := preparedIntegerStep_exec (body := body)
    hQ hA hW hP hs hst hu hn v₁ S₁ tailX (S.R 111) hctx₁.rows hctx₁.width
    (by simpa [S₁] using hcount) (by simpa [S₁] using hprecision)
    (by simpa [S₁] using hiteration) (by simpa [S₁] using hsaved) hctx₁.column
    (by simp [S₁, factors]) hctx₁.clean hctx₁.ready hctx₁.work
    (by simpa [S₁] using hrest) (by simpa [S₁] using hexponent)
  let next := cstream A w (rowColumnWords P s t u band L (n + 1))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update S₁.R 111 (S.R 111))
    113 (next ++ S₁.R 113)) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := replaceColumn_exec (body := body)
    (show [(102 : Fin 117), 94, 99, 110, 113, 104, 105].Nodup by decide) L w v₂ S₂
    (cstream A w (rowColumnWords P s t u band L n)) next tailX (S.R 113)
    (by simpa [S₂, S₁] using hctx.rows) (by simpa [S₂, S₁] using hctx.width)
    (by simpa [S₂, S₁] using hctx.column) (by simp [S₂, S₁])
    (by simp [rowColumnWords]) (by simp [next, rowColumnWords])
    (by simpa [S₂, S₁] using hctx.work 99 (by simp [integerRowWork]))
    (by simpa [S₂, S₁] using hctx.work 104 (by simp [integerRowWork]))
    (by simpa [S₂, S₁] using hctx.work 105 (by simp [integerRowWork]))
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update S₂.R 110 (next ++ tailX)) 113 (S.R 113)) }
  have hpush : (pushOne 116 : Act 117 Q A U).run (mk v₃ S₃) =
      mk v₃ { S₃ with R := Function.update S₃.R 116 (tick :: S₃.R 116) } := by
    simp [pushOne, Action.run, update_rt]
  refine ⟨v₃, m₁ + (m₂ + (m₃ + 1)), hu₃.trans (hu₂.trans hu₁), ?_, ?_, ?_⟩
  · unfold integerIterationCost
    nlinarith only [hm₁, hm₂, hm₃]
  · refine (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃
      (hpush ▸ Exec.act (body := body) (pushOne 116) (mk v₃ S₃))))).cast rfl ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hi : k = 116
    · subst k; simp [S₃, S₂, S₁, iteratedColumn]
    by_cases hx : k = 110
    · subst k; simp [S₃, S₂, S₁, iteratedColumn, next]
    by_cases hf : k = 111
    · subst k; simp [S₃, S₂, S₁, iteratedColumn]
    by_cases ho : k = 113
    · subst k; simp [S₃, iteratedColumn]
    simp [S₃, S₂, S₁, iteratedColumn, hi, hx, ho]
  · apply (hctx.replaceColumn (by simp [rowColumnWords]) ?_).update 116 (by simp)
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hfits i (List.mem_range.mp hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
