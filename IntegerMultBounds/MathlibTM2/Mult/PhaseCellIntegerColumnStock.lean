module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIterationsSetupStock

/-! Generate the unit seed and readiness once around the shared inverse recurrence. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem initializeIntegerColumn_native :
    mnNativePushBound 3 (initializeIntegerColumn (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [initializeIntegerColumn,generateSeed,seedBit,pushOne,unaryProduct,transfer,transferAct,
    copyR,copyStep,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

@[irreducible] def generatedIntegerColumnWorkspace (C L w M : ℕ) : ℕ :=
  3*(10*(L*w)+9*L+6*w+18)+prepareIntegerIterationsWorkspace C L w M

theorem generateIntegerColumn_trace_within (hQ : SS.states ≤ Q) (C L w M m₁ m₂ : ℕ)
    (v₀ v₁ v₂ : HS 117 Q A U) (S₀ S₁ S₂ : Stacks 117 A)
    (h₁ : Exec body initializeIntegerColumn (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+prepareIntegerIterationsWorkspace C L w M)
      depth (prepareIntegerIterations hQ) (mk v₁ S₁) m₂ (mk v₂ S₂))
    (hm₁ : m₁ ≤ 10*(L*w)+9*L+6*w+18) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+generatedIntegerColumnWorkspace C L w M)
      depth (generateIntegerColumn hQ) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) := by
  have ht₁ := mn_native_exec_within h₁ 3 initializeIntegerColumn_native depth
    (mnSize (mk v₀ S₀)+depth+3*(10*(L*w)+9*L+6*w+18)) (by omega)
  exact (mn_seq_within_add ht₁ (h₂ depth)).mono (by
    intro d z hz; simpa only [generatedIntegerColumnWorkspace] using hz)

theorem generateIntegerColumn_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L w M : ℕ} (hW : P * (M + 2) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailF : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hrowCount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hsavedRows : S.R 108 = []) (hcount : (S.R 101).length = M) (hsaved : S.R 100 = [])
    (hfactor : S.R 109 = cstream A w ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ prepareCost 0 w + M * (integerIterationCost L w + 5) + 10 * (L * w) + 9 * L + 6 * P + 22 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+generatedIntegerColumnWorkspace C L w M)
        depth (generateIntegerColumn hQ) (mk v S) m
        (mk v' (generatedColumn S w (rowColumnWords P s t u band L (M + 1)) (M + 1)))) ∧
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
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hctx₂⟩ := prepareIntegerIterations_exec_within (body := body) (n := 1) (M := M) (band := band)
    hQ hA hW' hP hs hst hu (by decide) C hpush v₁ SI (S.R 110) tailF
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
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, (fun depth => (generateIntegerColumn_trace_within hQ C L w M m₁ m₂
    v v₁ v₂ S SI _ he₁ he₂ (by nlinarith only [hm₁,hPW]) depth).cast rfl (congrArg (mk v₂) hstate)), hstate ▸ hctx₂⟩
  nlinarith only [hm₁, hm₂]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
