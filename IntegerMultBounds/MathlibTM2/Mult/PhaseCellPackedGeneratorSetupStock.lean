module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGeneratorSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratorSetupStock

/-! Packing the shared inverse setup adds native linear traffic and retires the raw column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem packGenerators_native :
    mnNativePushBound 8 (packGenerators (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [packGenerators,unaryProduct,releasePrefix,takePrefix,transfer,transferAct,
    clearWords,umul,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

@[irreducible] def packedGeneratorSetupWorkspace (C L q W M : ℕ) : ℕ :=
  generatorSetupWorkspace C L q W M+8*packGeneratorsCost L W q

theorem generatePackedGenerators_trace_within (hQ : SS.states ≤ Q) (C L q W M m₁ m₂ : ℕ)
    (v₀ v₁ v₂ : HS 117 Q A U) (S₀ S₁ S₂ : Stacks 117 A)
    (h₁ : ∀ depth, ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+generatorSetupWorkspace C L q W M)
      depth (generateGenerators hQ) (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : Exec body packGenerators (mk v₁ S₁) m₂ (mk v₂ S₂))
    (hm₂ : m₂ ≤ packGeneratorsCost L W q) (depth : ℕ) :
    ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+packedGeneratorSetupWorkspace C L q W M)
      depth (generatePackedGenerators hQ) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) := by
  have ht₂ := mn_native_exec_within h₂ 8 packGenerators_native depth
    (mnSize (mk v₁ S₁)+depth+8*packGeneratorsCost L W q) (by omega)
  exact (mn_seq_within_add (h₁ depth) ht₂).mono (by
    intro d z hz; simpa only [packedGeneratorSetupWorkspace] using hz)

theorem generatePackedGenerators_exec_within (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q W M : ℕ} (hW : P * (M + 2) + 3 ≤ W) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (hqr : q ≤ P * (M + 1) + 1)
    (hwidth : P * (M + 1) + 1 - q + (2 * q + 8) ≤ W)
    (hd : q + P * (M + 1) < W) (hw : 2 * q + 8 ≤ W)
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
    ∃ v' m, v'.user = v.user ∧ m ≤ generatorSetupCost P M L q W + packGeneratorsCost L W q ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+packedGeneratorSetupWorkspace C L q W M)
        depth (generatePackedGenerators hQ) (mk v S) m
        (mk v' (packedGeneratorBank S P s t u band L q W (M + 1)))) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := generateGenerators_exec_within (body := body) (band := band)
    hQ hA hW hP hs hst hu hL hqr hwidth hd hw C hpush v S tailF hrows hwR hrowCount
    hprecision hq hsavedRows hcount hsaved hfactor hc hblank hfresh
  let S₁ := generatorBank S P s t u band L q W (M + 1)
  have hsmall (k : Fin 117) (hk : k ∈ [(94 : Fin 117), 98, 99, 102, 104, 105, 112]) :
      S₁.R k = S.R k := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [S₁, generatorBank, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := packGenerators_exec (body := body) L W q
    (rowColumnWords P s t u band L (M + 1)) (columnWords P s t u band L q (M + 1))
    (reversedColumnWords P s t u band L q (M + 1)) (reciprocalWord P s t u band L q (M + 1))
    (by simp [rowColumnWords]) (by simp) (by simp) v₁ S₁ (S.R 110) (S.R 111) (S.R 113)
    (by rw [hsmall 102 (by simp)]; exact hrows)
    (by rw [hsmall 94 (by simp)]; exact hwR) (by rw [hsmall 112 (by simp)]; exact hq)
    (by simp [S₁, generatorBank, encodedColumnBank, generatedColumn])
    (by simp [S₁, generatorBank, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code])
    (by simp [S₁, generatorBank, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code])
    (by simp [S₁, generatorBank])
    (by
      intro k hk
      rw [hsmall k (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hk ⊢
        tauto)]
      exact hfresh k ((by decide : [(98 : Fin 117), 99, 104, 105].Sublist
        [96, 97, 98, 99, 104, 105, 106, 107, 113, 115, 116]).subset hk))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, (fun depth => (generatePackedGenerators_trace_within hQ C L q W M m₁ m₂
    v v₁ v₂ S S₁ _ he₁ he₂ hm₂ depth).cast rfl ?_)⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases h96 : k = 96
  · subst k; simp [packedGeneratorBank, counterR, cr, OutputPlacement.code, hfresh 96 (by simp)]
  by_cases h110 : k = 110
  · subst k
    simp [packedGeneratorBank, generatorPage, List.append_assoc]
  by_cases h111 : k = 111
  · subst k; simp [packedGeneratorBank, counterR, cr, OutputPlacement.code]
  by_cases h113 : k = 113
  · subst k; simp [packedGeneratorBank, counterR, cr, OutputPlacement.code]
  simp [S₁, generatorBank, encodedColumnBank, generatedColumn, packedGeneratorBank, h96, h110, h111, h113, Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
