module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLineSizes

/-! The factorizer's physical tables are the tables of the natural-order line solve. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.MathlibTM2.Mult.BandList

def naturalLineLc (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) : List (List ℤ) :=
  (factorRowsZ q K (windowZ W AZ) (inputsZ W AZ N)).map Prod.fst

def naturalLineUc (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) : List (List ℤ) :=
  (List.range N).reverse.map (ucolZ W
    ((factorRowsZ q K (windowZ W AZ) (inputsZ W AZ N)).map Prod.snd))

def naturalLineRcs (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) : List ℤ :=
  ((factorRowsZ q K (windowZ W AZ) (inputsZ W AZ N)).map
    (fun c => newtonZ q (c.2.headD 0) K)).reverse

theorem naturalLineTables_lengths (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) :
    (naturalLineLc q K W N AZ).length = N ∧
    (naturalLineUc q K W N AZ).length = N ∧ (naturalLineRcs q K W N AZ).length = N := by
  simp [naturalLineLc,naturalLineUc,naturalLineRcs,factorRowsZ_facState,inputsZ]

/-- Exact identification with the forward multipliers, upper columns and reciprocal
records emitted by the physical factorizer. -/
theorem naturalLineTables_factor (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) :
    (naturalLineLc q K W N AZ).flatten = facLf q K (windowZ W AZ) (inputsZ W AZ N) N ∧
    naturalLineUc q K W N AZ = (List.range N).reverse.map
      (ucolZ W (facUr q K (windowZ W AZ) (inputsZ W AZ N) N)) ∧
    naturalLineRcs q K W N AZ = (List.range N).reverse.map (fun j =>
      newtonZ q (facPiv (facState q K (windowZ W AZ) (inputsZ W AZ N) j)) K) := by
  have hfac := factorRowsZ_facState q K (inputsZ W AZ N) (windowZ W AZ)
  have hlen : (inputsZ W AZ N).length = N := by simp [inputsZ]
  rw [hlen] at hfac
  simp [naturalLineLc,naturalLineUc,naturalLineRcs,hfac,facLf,facUr,facPiv,
    List.map_map,List.map_reverse,Function.comp_def]

theorem naturalLineSolve_re (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) (b : List GaussianInt) :
    (bandSolveVec q W (naturalLineLc q K W N AZ) (naturalLineUc q K W N AZ)
      (naturalLineRcs q K W N AZ) b).map (·.re) = lineSolveZ q K W N AZ (b.map (·.re)) := by
  rw [bandSolveVec_re]
  simp only [naturalLineLc,naturalLineUc,naturalLineRcs,lineSolveZ,← List.range_eq_range',List.map_map,Function.comp_def]

theorem naturalLineSolve_im (q K W N : ℕ) (AZ : ℕ → ℕ → ℤ) (b : List GaussianInt) :
    (bandSolveVec q W (naturalLineLc q K W N AZ) (naturalLineUc q K W N AZ)
      (naturalLineRcs q K W N AZ) b).map (·.im) = lineSolveZ q K W N AZ (b.map (·.im)) := by
  rw [bandSolveVec_im]
  simp only [naturalLineLc,naturalLineUc,naturalLineRcs,lineSolveZ,← List.range_eq_range',List.map_map,Function.comp_def]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
