module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerRowData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeedFormat

/-! # One executed integer inverse-generator iteration

Rows run in descending order, so prepending their results produces the next
column in its existing order. The loop consumes the stated factor/RHS pages;
generating those pages and controlling repeated iterations remain separate.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

def generatorRowJobs (P s t u band L n : ℕ) : List (List GaussianInt × GaussianInt) :=
  (List.range L).reverse.map (fun i => (rowFactorWords P s t u band L i,
    (⟨(2 : ℤ) ^ (P * (n + 1)) * (if i = 0 then 1 else 0), 0⟩ : GaussianInt)))

@[simp] theorem generatorRowJobs_length (P s t u band L n : ℕ) :
    (generatorRowJobs P s t u band L n).length = L := by simp [generatorRowJobs]

/-- The factor page is independent of the iteration count and its RHS scale. -/
theorem generatorRowJobs_factors (P s t u band L n : ℕ) :
    (generatorRowJobs P s t u band L n).flatMap Prod.fst =
      (List.range L).reverse.flatMap (rowFactorWords P s t u band L) := by
  simp only [generatorRowJobs, List.flatMap_map]

theorem generatorRowJobs_factor_length (P s t u band L n : ℕ) :
    ((generatorRowJobs P s t u band L n).flatMap Prod.fst).length = L * L := by
  rw [generatorRowJobs_factors, List.length_flatMap]
  simp [rowFactorWords]

/-- The descending RHS page is the scaled-unit seed in reverse word order. -/
theorem generatorRowJobs_rhs (P s t u band L n : ℕ) :
    (generatorRowJobs P s t u band L n).map Prod.snd = (seedWords (P * (n + 1)) L).reverse := by
  simp [generatorRowJobs, seedWords, List.map_map, mul_ite]

/-- Descending execution and prefix publication cancel, with no free output permutation. -/
theorem generatorRowJobs_results (P s t u band L n : ℕ) :
    ((generatorRowJobs P s t u band L n).map
      (ScalarPlacement.integerRowResult (rowColumnWords P s t u band L n))).reverse =
      rowColumnWords P s t u band L (n + 1) := by
  simp only [generatorRowJobs, List.map_map, List.map_reverse, List.reverse_reverse, rowColumnWords]
  apply List.map_congr_left
  intro i hi
  exact rowResult_eq (List.mem_range.mp hi)

theorem generatorRowJobs_fits {P s t u band L n w : ℕ} (hW : P + 2 ≤ w) (hP : 13 ≤ P) :
    ∀ job ∈ generatorRowJobs P s t u band L n,
      job.1.length = L ∧ ∀ a ∈ job.1, Fits w a ∧ a.im = 0 := by
  intro job hj
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
  refine ⟨by simp [rowFactorWords], ?_⟩
  intro a ha
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
  refine ⟨?_, rfl⟩
  by_cases hki : k = i
  · simp only [hki, ite_true]
    constructor <;> simp
  · simpa only [hki, ite_false] using
      coefficientNumerator_fits hW hP s t u band (ToeplitzInverse.gap i k)

namespace ScalarPlacement

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- All rows execute through the actual staged kernel. Input and output signed
fits follow from the structural generator bounds; no row execution is supplied. -/
theorem integerGeneratorStep_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {P s t u band L n w : ℕ} (hW : P * (n + 1) + 3 ≤ w) (hP : 13 ≤ P)
    (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u) (hn : 1 ≤ n)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailA tailR : List (Fin (A + 4)))
    (hL : (S.R 102).length = L) (hwR : (S.R 94).length = w)
    (hcount : (S.R 103).length = L) (hsaved : S.R 108 = [])
    (hx : S.R 110 = cstream A w (rowColumnWords P s t u band L n) ++ tailX)
    (ha : S.R 111 = cstream A w ((generatorRowJobs P s t u band L n).flatMap Prod.fst) ++ tailA)
    (hr : S.R 112 = cstream A w ((generatorRowJobs P s t u band L n).map Prod.snd) ++ tailR)
    (hc : CClean mul S) (hready : Ready (fun r => S.R (cr r)) w 0)
    (hwork : ∀ k ∈ integerRowWork, S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ L * (integerRowCost L w + 5) + 4 ∧
      Exec body (integerRows hQ) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R 111 tailA) 112 tailR)
          113 (cstream A w (rowColumnWords P s t u band L (n + 1)) ++ S.R 113)) }) ∧
      ∀ i < L, Fits w (⟨(columnNumerators P s t u band L (n + 1)).getD i 0, 0⟩ : GaussianInt) := by
  have hcolW : P * n + 3 ≤ w := by nlinarith
  have hcoefW : P + 2 ≤ w := by nlinarith
  have hctx : IntegerRowContext L w (rowColumnWords P s t u band L n) tailX S := by
    refine ⟨by nlinarith, by simp [rowColumnWords], ?_, hL, hwR, hx, hc, hready, hwork⟩
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact columnNumerator_fits hcolW hP hs hst hu hn k (List.mem_range.mp hk)
  obtain ⟨v', m, hv, hm, he⟩ := integerRows_exec (body := body) hQ hA
    (rowColumnWords P s t u band L n) (generatorRowJobs P s t u band L n) v S tailX tailA tailR hctx
    (generatorRowJobs_fits hcoefW hP) (by simpa using hcount) hsaved ha hr
  refine ⟨v', m, hv, by simpa using hm, ?_, ?_⟩
  · simpa only [generatorRowJobs_results] using he
  · intro i hi
    exact columnNumerator_fits hW hP hs hst hu (by omega) i hi

end ScalarPlacement

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
