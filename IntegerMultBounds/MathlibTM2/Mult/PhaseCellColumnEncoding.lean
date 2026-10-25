module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicEncode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodingCounters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeRange

/-! # Generate the actual runtime column words with paid counters

All slice counters are generated from retained P/n/q/W headers and released.
The raw integer column survives for reciprocal and second-branch generation.
Only the encoded column prefix is published.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.ToeplitzInverse

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateColumnEncoding : Pr P₀ 117 Q A U :=
  .seq prepareColumnEncoding (.seq encodeDyadicColumn (clearWords [115, 98, 107]))

theorem generateColumnEncoding_exec (P s t u band L n q W : ℕ) (hn : 1 ≤ n)
    (hscale : P * n + 1 ≤ W) (hqr : q ≤ P * n + 1)
    (hwidth : P * n + 1 - q + (2 * q + 8) ≤ W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hW : (S.R 94).length = W)
    (hP : (S.R 114).length = P) (hnR : (S.R 116).length = n) (hq : (S.R 112).length = q)
    (hsrc : S.R 110 = cstream A W (rowColumnWords P s t u band L n) ++ tailX)
    (hfresh : ∀ k ∈ [(115 : Fin 117), 98, 107, 99, 104, 105, 113, 96], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ L * (20 * W + 6 * (2 * q + 8) + 23) + 31 * W + 57 ∧
      Exec body generateColumnEncoding (mk v S) m
        (mk v' { S with R := (Function.update S.R 111
          (cstream A (2 * q + 8) (columnWords P s t u band L q n) ++ S.R 111)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepareColumnEncoding_exec (body := body) P n q W hn hscale hqr hwidth
    v S hP hnR hq hW (fun k hk => hfresh k ((by decide : [(115 : Fin 117), 98, 107, 104, 105].Sublist
      [115, 98, 107, 99, 104, 105, 113, 96]).subset hk))
  let S₁ := encodingCounterBank S W q (P * n + 1)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := encodeDyadicColumn_exec (body := body) L W (2 * q + 8) q (P * n + 1)
    (by omega) hqr hwidth (columnNumerators P s t u band L n) (by simp) v₁ S₁ tailX
    (by simpa [S₁, encodingCounterBank] using hrows) (by simpa [S₁, encodingCounterBank] using hW)
    (by simpa [S₁, encodingCounterBank, rowColumnWords_eq] using hsrc)
    (encodingCounterBank_ready S W q (P * n + 1) (hfresh 105 (by simp)))
    (by
      intro k hk
      have hk' := (by decide : [(99 : Fin 117), 104, 113, 96].Sublist
        [115, 98, 107, 99, 104, 105, 113, 96]).subset hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;>
        simpa [S₁, encodingCounterBank] using hfresh _ hk')
  let encoded := cstream A (2 * q + 8)
    ((columnNumerators P s t u band L n).map (dyadicWord q (P * n + 1)))
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 111 (encoded ++ S₁.R 111) }
  obtain ⟨v₃, hu₃, he₃⟩ := clearWords_exec (body := body) [115, 98, 107] (by decide) v₂ S₂
  have hsum : ([(115 : Fin 117), 98, 107].map (fun k => (S₂.R k).length)).sum = W := by
    simp [S₂, S₁, encodingCounterBank]
    omega
  have hformat : (columnNumerators P s t u band L n).map (dyadicWord q (P * n + 1)) =
      columnWords P s t u band L q n := integerColumnWords_eq P s t u band L q n
  refine ⟨v₃, m₁ + (m₂ + (2 * W + 7)), hu₃.trans (hu₂.trans hu₁), by omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases ho : k = 111
  · subst k; simp [S₂, S₁, encodingCounterBank, encoded, hformat]
  by_cases hk : k ∈ [(115 : Fin 117), 98, 107]
  · have hk' := (by decide : [(115 : Fin 117), 98, 107].Sublist
      [115, 98, 107, 99, 104, 105, 113, 96]).subset hk
    simp [hk, ho, hfresh k hk']
  · have hne : k ≠ 115 ∧ k ≠ 98 ∧ k ≠ 107 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hk
    simp [hk, ho, S₂, S₁, encodingCounterBank, hne.1, hne.2.1, hne.2.2]

/-- Signed decoding of the emitted runtime word recovers the model without aliasing. -/
theorem encodedColumn_decode {A P s t u band L q n : ℕ} (hA : 4 ≤ A) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hq : 2 ≤ q) (hn : 1 ≤ n)
    (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hsrc : S.R 111 = cstream A (2 * q + 8) (columnWords P s t u band L q n) ++ tail)
    (i : ℕ) (hi : i < L) :
    decodeWord (((S.R 111).drop (i * (2 * q + 8))).take (2 * q + 8)) =
      block (columnWords P s t u band L q n) i := by
  have hi' : i < (columnWords P s t u band L q n).length := by simpa using hi
  rw [hsrc, cstream_word _ _ tail i hi', decodeWord_of_fits hA (by omega) _
    (fits_of_disk (q := q) (by omega) _ (columnWords_disk hP hs hst hu hq hn _ (List.getElem_mem hi')))]
  simp only [block, List.getElem?_eq_getElem hi', Option.getD_some]

theorem encodedColumn_error_precision {A P s t u band L q j : ℕ} (hA : 4 ≤ A) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hq : j + 2 ≤ q)
    (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hsrc : S.R 111 = cstream A (2 * q + 8) (columnWords P s t u band L q (j + 2)) ++ tail)
    (i : ℕ) (hi : i < L) :
    |2 * (value q (decodeWord (((S.R 111).drop (i * (2 * q + 8))).take (2 * q + 8)))).re -
      col (natInv L (PhaseCellToeplitz.coeff P s t u band)) i| ≤ 1 / (2 : ℝ) ^ j := by
  rw [encodedColumn_decode hA hP hs hst hu (by omega) (by omega) S tail hsrc i hi]
  exact columnWords_error_precision hP hs hst hu hq i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
