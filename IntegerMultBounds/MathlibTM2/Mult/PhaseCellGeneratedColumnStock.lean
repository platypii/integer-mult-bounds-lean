module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerColumnStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellColumnEncodingStock

/-! The executed inverse recurrence and bit encoding retain their separate shared reserves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.ToeplitzInverse
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

@[irreducible] def generatedEncodedColumnWorkspace (C L q W M : ℕ) : ℕ :=
  generatedIntegerColumnWorkspace C L W M+columnEncodingWorkspace L q W

theorem generateEncodedColumn_trace_within (hQ : SS.states ≤ Q) (C L q W M m₁ m₂ : ℕ)
    (v₀ v₁ v₂ : HS 117 Q A U) (S₀ S₁ S₂ : Stacks 117 A)
    (h₁ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+generatedIntegerColumnWorkspace C L W M)
      depth (generateIntegerColumn hQ) (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+columnEncodingWorkspace L q W)
      depth generateColumnEncoding (mk v₁ S₁) m₂ (mk v₂ S₂)) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+generatedEncodedColumnWorkspace C L q W M)
      depth (generateEncodedColumn hQ) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) := by
  exact (mn_seq_within_add (h₁ depth) (h₂ depth)).mono (by
    intro d z hz; simpa only [generatedEncodedColumnWorkspace] using hz)

theorem generateEncodedColumn_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q W M : ℕ} (hW : P * (M + 2) + 3 ≤ W) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (hqr : q ≤ P * (M + 1) + 1)
    (hwidth : P * (M + 1) + 1 - q + (2 * q + 8) ≤ W)
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ C)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailF : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hwR : (S.R 94).length = W)
    (hrowCount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hq : (S.R 112).length = q)
    (hsavedRows : S.R 108 = []) (hcount : (S.R 101).length = M) (hsaved : S.R 100 = [])
    (hfactor : S.R 109 = cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 113, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ prepareCost 0 W + M * (integerIterationCost L W + 5) +
        L * (30 * W + 6 * (2 * q + 8) + 32) + 31 * W + 6 * P + 79 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+generatedEncodedColumnWorkspace C L q W M)
        depth (generateEncodedColumn hQ) (mk v S) m
        (mk v' (encodedColumnBank S P s t u band L q W (M + 1)))) ∧
      IntegerGeneratorContext P s t u band L (M + 1) W (S.R 110) tailF
        (encodedColumnBank S P s t u band L q W (M + 1)) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hctx⟩ := generateIntegerColumn_exec_within (body := body)
    (band := band) hQ hA hW hP hs hst hu hL C hpush v S tailF hrows hwR hrowCount hprecision
    hsavedRows hcount hsaved hfactor hc hblank
    (fun k hk => hfresh k ((by decide : [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 115, 116].Sublist
      [96, 97, 98, 99, 104, 105, 106, 107, 113, 115, 116]).subset hk))
  let S₁ := generatedColumn S W (rowColumnWords P s t u band L (M + 1)) (M + 1)
  have hq₁ : (S₁.R 112).length = q := by
    simpa [S₁, generatedColumn, counterR, cr, OutputPlacement.code] using hq
  have hfresh₁ : ∀ k ∈ [(115 : Fin 117), 98, 107, 99, 104, 105, 113, 96], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simpa [S₁, generatedColumn, counterR, cr, OutputPlacement.code] using hfresh _ (by simp)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := generateColumnEncoding_exec_within (body := body)
    P s t u band L (M + 1) q W (by omega) (by nlinarith) hqr hwidth
    v₁ S₁ (S.R 110) hctx.row.rows hctx.row.width hctx.precision hctx.iteration hq₁
    hctx.row.column hfresh₁
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, (fun depth => generateEncodedColumn_trace_within hQ C L q W M m₁ m₂
      v v₁ v₂ S S₁ _ he₁ he₂ depth),
    hctx.update 111 (by simp) _⟩
  nlinarith only [hm₁, hm₂]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
