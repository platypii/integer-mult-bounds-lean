module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalLineTables
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorIntegerMatrix

/-! The emitted boundary-page factors have exactly the natural solve's table layout. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {A s : ℕ} [NeZero s]

theorem boundaryFactor_solve_tables (q w K : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (σ : RsbR → List (Fin (A+4))) :
    let rows := factorIntegerRows (factorWindowValues B W columns)
    let inputs := factorIntegerRows (factorInputValues B W B.card columns)
    let AZ := factorRankIntegerMatrix B W columns
    σ .bo = cstream A w ((facLf q K rows inputs B.card).map fun x => (⟨x,0⟩ : GaussianInt)) →
    σ .hf = cstream A w ((List.range B.card).reverse.map fun m =>
      colC (ucolZ W (facUr q K rows inputs B.card) m)).flatten →
    σ .df = cstream A w ((List.range B.card).reverse.map fun j =>
      (⟨newtonZ q (facPiv (facState q K rows inputs j)) K,0⟩ : GaussianInt)) →
    σ .bo = cstream A w ((naturalLineLc q K W B.card AZ).map colC).flatten ∧
    σ .hf = cstream A w ((naturalLineUc q K W B.card AZ).map colC).flatten ∧
    σ .df = cstream A w ((naturalLineRcs q K W B.card AZ).map fun x => (⟨x,0⟩ : GaussianInt)) := by
  dsimp only
  intro hbo hhf hdf
  rw [factorWindowIntegers_windowZ,factorInputIntegers_inputsZ] at hbo hhf hdf
  obtain ⟨hL,hU,hr⟩ := naturalLineTables_factor q K W B.card (factorRankIntegerMatrix B W columns)
  refine ⟨?_,?_,?_⟩
  · rw [hbo]
    congr 1
    rw [← hL]
    rw [List.map_flatten]
    rfl
  · rw [hU,List.map_map]
    exact hhf
  · rw [hr,List.map_map]
    exact hdf

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
