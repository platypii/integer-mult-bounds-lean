module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerColumnAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellColumnEncoding

/-! # Generate and encode the inverse column in one executed program

The factor page remains borrowed. The raw signed column is retained for the
reciprocal and reversed branch; runtime words are prefixed to the output bank.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.ToeplitzInverse

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def generateEncodedColumn (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (generateIntegerColumn hQ) generateColumnEncoding

def encodedColumnBank {A : ℕ} (S : Stacks 117 A) (P s t u band L q W n : ℕ) : Stacks 117 A :=
  let S₁ := generatedColumn S W (rowColumnWords P s t u band L n) n
  { S₁ with R := (Function.update S₁.R 111
      (cstream A (2 * q + 8) (columnWords P s t u band L q n) ++ S₁.R 111)) }

/-- Both the recurrence and bit encoding execute from ordinary headers and the
retained factor page. All borrowed suffixes survive. -/
theorem generateEncodedColumn_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L q W M : ℕ} (hW : P * (M + 2) + 3 ≤ W) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hL : 0 < L)
    (hqr : q ≤ P * (M + 1) + 1)
    (hwidth : P * (M + 1) + 1 - q + (2 * q + 8) ≤ W)
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
      Exec body (generateEncodedColumn hQ) (mk v S) m
        (mk v' (encodedColumnBank S P s t u band L q W (M + 1))) ∧
      IntegerGeneratorContext P s t u band L (M + 1) W (S.R 110) tailF
        (encodedColumnBank S P s t u band L q W (M + 1)) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hctx⟩ := generateIntegerColumn_exec (body := body)
    (band := band) hQ hA hW hP hs hst hu hL v S tailF hrows hwR hrowCount hprecision
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
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := generateColumnEncoding_exec (body := body)
    P s t u band L (M + 1) q W (by omega) (by nlinarith) hqr hwidth
    v₁ S₁ (S.R 110) hctx.row.rows hctx.row.width hctx.precision hctx.iteration hq₁
    hctx.row.column hfresh₁
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂,
    hctx.update 111 (by simp) _⟩
  nlinarith only [hm₁, hm₂]

/-- The published bank has the error required by the cell kernel, while the
raw column and its signed context remain available for reciprocal generation. -/
theorem encodedColumnBank_error {A P s t u band L q W j : ℕ}
    (hA : 4 ≤ A) (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hq : j + 2 ≤ q) (S : Stacks 117 A) (i : ℕ) (hi : i < L) :
    let S' := encodedColumnBank S P s t u band L q W (j + 2)
    |2 * (value q (decodeWord (((S'.R 111).drop (i * (2 * q + 8))).take (2 * q + 8)))).re -
      col
        (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤
      1 / (2 : ℝ) ^ j := by
  apply encodedColumn_error_precision hA hP hs hst hu hq _ (S.R 111) _ i hi
  simp [encodedColumnBank, generatedColumn, counterR, cr, OutputPlacement.code]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
