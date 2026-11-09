module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIterationsSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerIterationsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarNativeStock
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Arithmetic readiness is allocated once around the complete inverse recurrence. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def prepareIntegerIterationsWorkspace (C L w M : ℕ) : ℕ :=
  3*prepareCost 0 w+(4*M+integerIterationWorkspace C L w+2)

theorem prepareIntegerIterations_trace_within (hQ : SS.states ≤ Q) (C L w M m₁ m₂ : ℕ)
    (v₀ v₁ v₂ : HS 117 Q A U) (S₀ S₁ S₂ : Stacks 117 A)
    (h₁ : Exec body prepare (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+(4*M+integerIterationWorkspace C L w+2))
      depth (integerIterations hQ) (mk v₁ S₁) m₂ (mk v₂ S₂))
    (hm₁ : m₁ ≤ prepareCost 0 w) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+prepareIntegerIterationsWorkspace C L w M)
      depth (prepareIntegerIterations hQ) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) := by
  have ht₁ := mn_native_exec_within h₁ 3 prepare_native depth
    (mnSize (mk v₀ S₀)+depth+3*prepareCost 0 w) (by omega)
  exact (mn_seq_within_add ht₁ (h₂ depth)).mono (by
    intro d z hz; simpa only [prepareIntegerIterationsWorkspace] using hz)

theorem prepareIntegerIterations_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w M : ℕ} (hW : P * (n + M + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailF : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hrows : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hiteration : (S.R 116).length = n) (hsavedRows : S.R 108 = [])
    (hcount : (S.R 101).length = M) (hsaved : S.R 100 = [])
    (hx : S.R 110 = cstream A w (rowColumnWords P s t u band L n) ++ tailX)
    (hfactor : S.R 109 = cstream A w ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost 0 w + M * (integerIterationCost L w + 5) + 4 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+prepareIntegerIterationsWorkspace C L w M)
        depth (prepareIntegerIterations hQ) (mk v S) m
        (mk v' (iteratedColumns { S with R := counterR 0 w S.R } w
          (rowColumnWords P s t u band L (n + M)) tailX M))) ∧
      IntegerGeneratorContext P s t u band L (n + M) w tailX tailF
        (iteratedColumns { S with R := counterR 0 w S.R } w
          (rowColumnWords P s t u band L (n + M)) tailX M) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepare_exec_of_width (body := body) 0 w (by nlinarith) (by nlinarith)
    v S (by simp [hsaved]) hwR (by
      intro k hk
      exact (hc ⟨k.val, by omega⟩).2) (fun r _ => hblank r)
  let SP : Stacks 117 A := { S with R := counterR 0 w S.R }
  have hoff (k : Fin 117) (hk : 96 ≤ k.val) : SP.R k = S.R k := by
    have hne (r : CR) : k ≠ cr r := by
      have hr := (cr_range r).2.1
      intro he
      have hv := congrArg Fin.val he
      omega
    simp [SP, counterR, hne]
  have hcleanP : CClean mul SP := by
    intro i
    refine ⟨(hc i).1, ?_⟩
    simpa [SP, counterR, (cr_mul .wn i).symm, (cr_mul .pn i).symm, (cr_mul .nn i).symm] using (hc i).2
  have hworkP : ∀ k ∈ integerRowWork, SP.R k = [] := by
    intro k hk
    have hb : S.R k = [] := by
      simp only [integerRowWork, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | exact hblank _ | exact hfresh _ (by simp)
    have hd : integerRowWork.Disjoint [cr .wn, cr .pn, cr .nn] := by
      simp [integerRowWork, cr, OutputPlacement.code]
    have hne (r : CR) (hr : r ∈ [CR.wn, .pn, .nn]) : k ≠ cr r := by
      intro he
      subst k
      apply List.disjoint_left.mp hd hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp
    simpa [SP, counterR, hne .wn (by simp), hne .pn (by simp), hne .nn (by simp)] using hb
  have hcolW : P * n + 3 ≤ w := by
    have hm := Nat.mul_le_mul_left P (show n ≤ n + M + 1 by omega)
    omega
  have hrow : IntegerRowContext L w (rowColumnWords P s t u band L n) tailX SP := by
    refine ⟨by omega, by simp [rowColumnWords], ?_, ?_, ?_, ?_, hcleanP,
      counterR_ready 0 w S.R hblank, hworkP⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact columnNumerator_fits hcolW hP hs hst hu hn i (List.mem_range.mp hi)
    · simpa only [hoff 102 (by decide)] using hL
    · simpa [SP, counterR, cr, OutputPlacement.code] using hwR
    · simpa only [hoff 110 (by decide)] using hx
  have hctx : IntegerGeneratorContext P s t u band L n w tailX tailF SP := by
    refine ⟨hrow, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hoff 103 (by decide)] using hrows
    · simpa only [hoff 114 (by decide)] using hprecision
    · simpa only [hoff 116 (by decide)] using hiteration
    · simpa only [hoff 108 (by decide)] using hsavedRows
    · simpa only [hoff 109 (by decide)] using hfactor
    · simpa only [hoff 107 (by decide)] using hfresh 107 (by simp)
    · simpa only [hoff 115 (by decide)] using hfresh 115 (by simp)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hctx₂⟩ := integerIterations_exec_within (body := body) hQ hA C hpush hW hP hs hst hu hn
    v₁ SP tailX tailF hctx (by simpa only [hoff 101 (by decide)] using hcount)
    (by simpa only [hoff 100 (by decide)] using hsaved)
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, (fun depth => prepareIntegerIterations_trace_within hQ C L w M m₁ m₂
    v v₁ v₂ S SP _ he₁ he₂ hm₁ depth), hctx₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
