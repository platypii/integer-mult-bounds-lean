module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedColumn
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversedColumnAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerReciprocal

/-! # Execute both inverse generators and their reciprocal

The only supplied coefficient data are the retained factor page. All three
runtime word banks are constructed, with the raw column retained explicitly.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def generateGenerators (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (generateEncodedColumn hQ) (.seq generateReversedColumn generateReciprocal)

def generatorBank {A : ℕ} (S : Stacks 117 A) (P s t u band L q W n : ℕ) : Stacks 117 A :=
  let S₁ := encodedColumnBank S P s t u band L q W n
  { S₁ with R := (Function.update (Function.update S₁.R 113
    (cstream A (2 * q + 8) (reversedColumnWords P s t u band L q n) ++ S₁.R 113))
      96 (csyms A (2 * q + 8) (reciprocalWord P s t u band L q n))) }

def generatorSetupCost (P M L q W : ℕ) : ℕ :=
  prepareCost 0 W + M * (integerIterationCost L W + 5) +
    L * (30 * W + 6 * (2 * q + 8) + 32) + 31 * W + 6 * P + 79 +
    ((L - 1) * (16 * (2 * q + 8) + 21) + 4 * L + 12 * (2 * q + 8) + 4 * q + 31) +
    (W * (12 * W + 128) + 6 * (2 * q + 8) + 4 * q + 134)

/-- One paid setup program constructs the two generator vectors and reciprocal,
without assuming any precomputed column, inverse or reciprocal word bank. -/
theorem generateGenerators_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q W M : ℕ} (hW : P * (M + 2) + 3 ≤ W) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (hqr : q ≤ P * (M + 1) + 1)
    (hwidth : P * (M + 1) + 1 - q + (2 * q + 8) ≤ W)
    (hd : q + P * (M + 1) < W) (hw : 2 * q + 8 ≤ W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailF : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hwR : (S.R 94).length = W)
    (hrowCount : (S.R 103).length = L) (hprecision : (S.R 114).length = P)
    (hq : (S.R 112).length = q)
    (hsavedRows : S.R 108 = []) (hcount : (S.R 101).length = M) (hsaved : S.R 100 = [])
    (hfactor : S.R 109 = cstream A W ((List.range L).reverse.flatMap (rowFactorWords P s t u band L)) ++ tailF)
    (hc : CClean mul S) (hblank : ∀ r, S.R (cr r) = [])
    (hfresh : ∀ k ∈ [(96 : Fin 117), 97, 98, 99, 104, 105, 106, 107, 113, 115, 116], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatorSetupCost P M L q W ∧
      Exec body (generateGenerators hQ) (mk v S) m
        (mk v' (generatorBank S P s t u band L q W (M + 1))) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hctx⟩ := generateEncodedColumn_exec (body := body)
    (band := band) hQ hA hW hP hs hst hu hL hqr hwidth v S tailF hrows hwR hrowCount
    hprecision hq hsavedRows hcount hsaved hfactor hc hblank hfresh
  let S₁ := encodedColumnBank S P s t u band L q W (M + 1)
  have hq₁ : (S₁.R 112).length = q := by
    simpa [S₁, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code] using hq
  have hsrc : S₁.R 111 = cstream A (2 * q + 8) (columnWords P s t u band L q (M + 1)) ++ S.R 111 := by
    simp [S₁, encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code]
  have hfresh₁ : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106, 107], S₁.R k = [] := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hctx.rest
      | exact hctx.row.work _ (by simp [integerRowWork])
  obtain ⟨v₂, hu₂, he₂⟩ := generateReversedColumn_exec (body := body) (band := band)
    hL v₁ S₁ (S.R 111) hq₁ hctx.row.rows hsrc hfresh₁
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update S₁.R 113
    (cstream A (2 * q + 8) (reversedColumnWords P s t u band L q (M + 1)) ++ S₁.R 113)) }
  have hctx₂ : IntegerGeneratorContext P s t u band L (M + 1) W (S.R 110) tailF S₂ :=
    hctx.update 113 (by simp) _
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := generateIntegerReciprocal_exec (body := body) (band := band)
    (by omega) hP hs hst hu hL (by omega) hd hw v₂ S₂ (S.R 110) tailF hctx₂
    (by simpa [S₂] using hq₁)
  refine ⟨v₃, m₁ + (((L - 1) * (16 * (2 * q + 8) + 21) + 4 * L +
    12 * (2 * q + 8) + 4 * q + 31) + m₃), hu₃.trans (hu₂.trans hu₁), ?_,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  unfold generatorSetupCost
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
