module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupFits

/-! # The executed integer row is the next inverse-generator entry

The row arithmetic is specialized to the actual dyadic recurrence. Width
hypotheses discharge operand and result fits; there is no supplied row oracle.
The operand streams and scaled RHS still require executed staging.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.NLogN.ToeplitzInverse

def rowColumnWords (P s t u band L n : ℕ) : List GaussianInt :=
  (List.range L).map (fun k => ⟨(columnNumerators P s t u band L n).getD k 0, 0⟩)

/-- Every row reuses the same stored column in its existing order. -/
theorem rowColumnWords_eq (P s t u band L n : ℕ) :
    rowColumnWords P s t u band L n =
      (columnNumerators P s t u band L n).map (fun z => (⟨z, 0⟩ : GaussianInt)) := by
  apply List.ext_getElem (by simp [rowColumnWords])
  intro k hk _
  simp only [rowColumnWords, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa [rowColumnWords] using hk)]

theorem rowColumnWords_getD (P s t u band L n i : ℕ) (hi : i < L) :
    (rowColumnWords P s t u band L n).getD i 0 =
      (⟨(columnNumerators P s t u band L n).getD i 0, 0⟩ : GaussianInt) := by
  rw [List.getD_eq_getElem _ _ (by simpa [rowColumnWords] using hi)]
  simp [rowColumnWords]

def rowFactorWords (P s t u band L i : ℕ) : List GaussianInt :=
  (List.range L).map (fun k => ⟨if k = i then 0 else coefficientNumerator P s t u band (gap i k), 0⟩)

theorem rowProducts_eq (P s t u band L n i : ℕ) :
    List.zipWith (· * ·) (rowColumnWords P s t u band L n) (rowFactorWords P s t u band L i) =
      (rowTerms P s t u band L n i).map (fun z => (⟨z, 0⟩ : GaussianInt)) := by
  simp only [rowColumnWords, rowFactorWords, rowTerms, List.map_map, List.zipWith_map]
  rw [List.zipWith_self]
  apply List.map_congr_left
  intro k _
  by_cases hk : k = i <;> ext <;> simp [hk, mul_comm]

theorem rowResult_eq {P s t u band L n i : ℕ} (hi : i < L) :
    (⟨(2 : ℤ) ^ (P * (n + 1)) * (if i = 0 then 1 else 0), 0⟩ : GaussianInt) -
      (List.zipWith (· * ·) (rowColumnWords P s t u band L n)
        (rowFactorWords P s t u band L i)).sum =
      ⟨(columnNumerators P s t u band L (n + 1)).getD i 0, 0⟩ := by
  rw [rowProducts_eq]
  have hsum (zs : List ℤ) :
      (zs.map (fun z => (⟨z, 0⟩ : GaussianInt))).sum = ⟨zs.sum, 0⟩ := by
    induction zs with
    | nil => rfl
    | cons z zs ih => simp only [List.map_cons, List.sum_cons, ih]; rfl
  rw [hsum, rowTerms_sum]
  have hget : (columnNumerators P s t u band L (n + 1)).getD i 0 =
      (2 : ℤ) ^ (P * (n + 1)) * (if i = 0 then 1 else 0) -
        generatorOffDiag (coefficientNumerator P s t u band)
          (columnNumerators P s t u band L n) i := by
    simp [columnNumerators, dyadicGeneratorIter, generatorStep, hi]
  rw [hget]
  rfl

namespace ScalarPlacement

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- The composed machine emits the next actual generator entry, with all
input/result widths derived from the existing structural setup bounds. -/
theorem generatorRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (i : ℕ) (hi : i < L) (v : HS 117 Q A U) (S : Stacks 117 A) (hc : CClean mul S)
    (hwork : ∀ r, r ∉ [CR.xs, .ys] → S.R (cr r) = [])
    (hqR : (S.R 100).length = 0) (hwR : (S.R 94).length = w)
    (hx : S.R (cr .xs) = cstream A w (rowColumnWords P s t u band L n))
    (hy : S.R (cr .ys) = cstream A w (rowFactorWords P s t u band L i))
    (hrhs : S.R 96 = csyms A w
      ⟨(2 : ℤ) ^ (P * (n + 1)) * (if i = 0 then 1 else 0), 0⟩)
    (hsaved : S.R 97 = []) (htmp : S.R 98 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ prepareCost 0 w + L * (rmulCost w + 13 * w + 12) + 10 ∧
      Exec body (integerRow hQ) (mk v S) m
        (mk v' { S with R := (Function.update (counterR 0 w S.R) 96
          (csyms A w ⟨(columnNumerators P s t u band L (n + 1)).getD i 0, 0⟩)) }) ∧
      Fits w (⟨(columnNumerators P s t u band L (n + 1)).getD i 0, 0⟩ : GaussianInt) := by
  have hcolW : P * n + 3 ≤ w := by nlinarith
  have hcoefW : P + 2 ≤ w := by nlinarith
  obtain ⟨v', m, hv, hm, he⟩ := integerRow_exec (body := body) hQ hA (by nlinarith)
    (rowColumnWords P s t u band L n) (rowFactorWords P s t u band L i)
    (by simp [rowColumnWords, rowFactorWords])
    (by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      exact columnNumerator_fits hcolW hP hs hst hu hn k (List.mem_range.mp hk))
    (by
      intro a ha
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      refine ⟨?_, rfl⟩
      by_cases hki : k = i
      · simp only [hki, ite_true]
        constructor <;> simp
      · simpa only [hki, ite_false] using coefficientNumerator_fits hcoefW hP s t u band (gap i k))
    v S _ hc hwork hqR hwR hx hy hrhs hsaved htmp
  refine ⟨v', m, hv, ?_, ?_, columnNumerator_fits hW hP hs hst hu (by omega) i hi⟩
  · simpa only [rowColumnWords, List.length_map, List.length_range] using hm
  · simpa only [rowResult_eq hi] using he

end ScalarPlacement

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
