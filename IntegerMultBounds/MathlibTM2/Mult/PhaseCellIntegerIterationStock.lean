module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIteration
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStepPreparedStock

/-! A complete inverse-column iteration retains one row reserve and native page traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem copyFactorPage_native {T : ℕ}
    (rows rowCount width square count src dst saved tmp : Fin T) :
    mnNativePushBound 3 (copyFactorPage (P := P₀) (Q := Q) (A := A) (U := U)
      rows rowCount width square count src dst saved tmp) := by
  simp [copyFactorPage,unaryProduct,copyPrefix,copyR,copyStep,transfer,transferAct,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem replaceColumn_native {T : ℕ} (rows width count src next buf tmp : Fin T) :
    mnNativePushBound 2 (replaceColumn (P := P₀) (Q := Q) (A := A) (U := U)
      rows width count src next buf tmp) := by
  simp [replaceColumn,unaryProduct,releasePrefix,takePrefix,transfer,transferAct,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

@[irreducible] def integerIterationWorkspace (C L w : ℕ) : ℕ :=
  3*(16*(L*L*w)+15*(L*L)+9*L+22)+
    (preparedIntegerStepWorkspace C L w+(2*(18*(L*w)+9*L+18)+1))

theorem integerIteration_trace_within (hQ : SS.states ≤ Q) (C L w m₁ m₂ m₃ : ℕ)
    (v₀ v₁ v₂ v₃ : HS 117 Q A U) (S₀ S₁ S₂ S₃ S₄ : Stacks 117 A)
    (h₁ : Exec body (copyFactorPage 102 103 94 107 99 109 111 104 105)
      (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+preparedIntegerStepWorkspace C L w)
      depth (preparedIntegerStep hQ) (mk v₁ S₁) m₂ (mk v₂ S₂))
    (h₃ : Exec body (replaceColumn 102 94 99 110 113 104 105) (mk v₂ S₂) m₃ (mk v₃ S₃))
    (h₄ : Exec body (.act (pushOne 116)) (mk v₃ S₃) 1 (mk v₃ S₄))
    (hm₁ : m₁ ≤ 16*(L*L*w)+15*(L*L)+9*L+22)
    (hm₃ : m₃ ≤ 18*(L*w)+9*L+18) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+integerIterationWorkspace C L w)
      depth (integerIteration hQ) (mk v₀ S₀) (m₁+(m₂+(m₃+1))) (mk v₃ S₄) := by
  have ht₁ := mn_native_exec_within h₁ 3 (copyFactorPage_native ..) depth
    (mnSize (mk v₀ S₀)+depth+3*(16*(L*L*w)+15*(L*L)+9*L+22)) (by omega)
  have ht₃ := mn_native_exec_within h₃ 2 (replaceColumn_native ..) depth
    (mnSize (mk v₂ S₂)+depth+2*(18*(L*w)+9*L+18)) (by omega)
  have ht₄ := mn_native_exec_within h₄ 1 (by simp [pushOne,mnNativePushBound,mnActPush]) depth
    (mnSize (mk v₃ S₃)+depth+1) (by omega)
  exact (mn_seq_within_add ht₁ (mn_seq_within_add (h₂ depth) (mn_seq_within_add ht₃ ht₄))).mono
    (by intro d z hz; simpa only [integerIterationWorkspace] using hz)

theorem integerIteration_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (C : ℕ) (hpushBound : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailF : List (Fin (A + 4)))
    (hctx : IntegerRowContext L w (rowColumnWords P s t u band L n) tailX S)
    (hcount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hiteration : (S.R 116).length = n) (hsaved : S.R 108 = [])
    (hfactor : S.R 109 = cstream A w ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hrest : S.R 107 = []) (hexponent : S.R 115 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ integerIterationCost L w ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+integerIterationWorkspace C L w)
        depth (integerIteration hQ) (mk v S) m
        (mk v' (iteratedColumn S w (rowColumnWords P s t u band L (n + 1)) tailX))) ∧
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
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hfits⟩ := preparedIntegerStep_exec_within (body := body)
    hQ hA hW hP hs hst hu hn C hpushBound v₁ S₁ tailX (S.R 111) hctx₁.rows hctx₁.width
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
  · intro depth
    refine (integerIteration_trace_within hQ C L w m₁ m₂ m₃
      v v₁ v₂ v₃ S S₁ S₂ S₃ _ he₁ he₂ he₃
      (hpush ▸ Exec.act (body := body) (pushOne 116) (mk v₃ S₃)) hm₁ hm₃ depth).cast rfl ?_
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
