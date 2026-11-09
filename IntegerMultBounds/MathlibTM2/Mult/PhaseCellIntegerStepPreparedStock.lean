module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStepPrepared
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerStepStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Scaled RHS construction uses linear traffic around the shared numerical row scan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem generateIterationRhs_native {T : ℕ}
    (rows width precision iteration dst exponent rowRest count saved savedPrefix tmp : Fin T) :
    mnNativePushBound 3 (generateIterationRhs (P₀ := P₀) (Q := Q) (A := A) (U := U)
      rows width precision iteration dst exponent rowRest count saved savedPrefix tmp) := by
  simp [generateIterationRhs,generateRhsPage,generateReverseSeed,generateSeed,seedBit,
    pushOne,popCount,unaryProduct,transfer,transferAct,copyR,copyStep,ucopy,umulSym,
    scanP,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,
    mnNativePushBound,mnActPush]

@[irreducible] def preparedIntegerStepWorkspace (C L w : ℕ) : ℕ :=
  3*(10*(L*w)+15*L+21*w+49)+(3*L+consumeIntegerRowWorkspace C L w+2)

theorem preparedIntegerStep_trace_within (hQ : SS.states ≤ Q) (C L w m₁ m₂ : ℕ)
    (v₀ v₁ v₂ : HS 117 Q A U) (S₀ S₁ S₂ : Stacks 117 A)
    (h₁ : Exec body (generateIterationRhs 102 94 114 116 112 115 107 99 104 106 105)
      (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+(3*L+consumeIntegerRowWorkspace C L w+2))
      depth (integerRows hQ) (mk v₁ S₁) m₂ (mk v₂ S₂))
    (hm₁ : m₁ ≤ 10*(L*w)+15*L+21*w+49) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+preparedIntegerStepWorkspace C L w)
      depth (preparedIntegerStep hQ) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) := by
  have ht₁ := mn_native_exec_within h₁ 3 (generateIterationRhs_native ..) depth
    (mnSize (mk v₀ S₀)+depth+3*(10*(L*w)+15*L+21*w+49)) (by omega)
  exact (mn_seq_within_add ht₁ (h₂ depth)).mono (by
    intro d z hz; simpa only [preparedIntegerStepWorkspace] using hz)

theorem preparedIntegerStep_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
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
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+preparedIntegerStepWorkspace C L w)
        depth (preparedIntegerStep hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update S.R 111 tailA) 113
          (cstream A w (rowColumnWords P s t u band L (n + 1)) ++ S.R 113)) })) ∧
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
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hfits⟩ := integerGeneratorStep_exec_within (body := body)
    hQ hA hW hP hs hst hu hn C hpush v₁ S₁ tailX tailA (S.R 112)
    (by simpa [S₁] using hL) (by simpa [S₁] using hwR)
    (by simpa [S₁] using hcount) (by simpa [S₁] using hsaved)
    (by simpa [S₁] using hx) (by simpa [S₁] using ha)
    (by simp [S₁, generatorRowJobs_rhs]) hclean₁ hready₁ hwork₁
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, (fun depth => (preparedIntegerStep_trace_within hQ C L w m₁ m₂
    v v₁ v₂ S S₁ _ he₁ he₂ (by nlinarith only [hm₁,hW,Nat.zero_le (P*n)]) depth).cast rfl ?_), hfits⟩
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
