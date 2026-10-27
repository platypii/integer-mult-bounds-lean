module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageValues
public import IntegerMultBounds.MathlibTM2.Fast.BandLine

/-! The emitted real Gaussian words are exactly the integer rows consumed by the factorizer. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

variable {s : ℕ} [NeZero s]

def factorIntegerRows (rows : List (List GaussianInt)) : List (List ℤ) :=
  rows.map (List.map (fun z : GaussianInt => z.re))

theorem factorIntegerRows_colC (rows : List (List GaussianInt))
    (hreal : ∀ row ∈ rows, ∀ z ∈ row, z.im = 0) :
    (factorIntegerRows rows).map colC = rows := by
  suffices h : rows.map (fun row => colC (row.map (fun z : GaussianInt => z.re))) = rows.map id by
    simpa [factorIntegerRows,List.map_map,Function.comp_def] using h
  apply List.map_congr_left (f := fun row => colC (row.map (fun z : GaussianInt => z.re))) (g := id)
  intro row hr
  simp only [colC,List.map_map]
  have h : row.map (fun z : GaussianInt => (⟨z.re, 0⟩ : GaussianInt)) = row.map id := by
    apply List.map_congr_left
    intro z hz
    ext <;> simp [hreal row hr z hz]
  simpa [Function.comp_def] using h

@[simp] theorem factorIntegerRows_length (rows : List (List GaussianInt)) :
    (factorIntegerRows rows).length = rows.length := by simp [factorIntegerRows]

theorem factorIntegerRows_row_length (rows : List (List GaussianInt)) (d : ℕ)
    (hrows : ∀ row ∈ rows, row.length = d) :
    ∀ row ∈ factorIntegerRows rows, row.length = d := by
  intro row hr
  change row ∈ rows.map (List.map (fun z : GaussianInt => z.re)) at hr
  obtain ⟨r,hmem,rfl⟩ := List.mem_map.mp hr
  simpa using hrows r hmem

theorem factorWindowIntegers_colC (B : Finset (ZMod s)) (W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) :
    (factorIntegerRows (factorWindowValues B W columns)).map colC = factorWindowValues B W columns := by
  apply factorIntegerRows_colC
  intro row hr z hz
  exact (factorWindowValues_format B W w columns hlen hformat row hr z hz).1

theorem factorInputIntegers_colC (B : Finset (ZMod s)) (W w L : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) :
    (factorIntegerRows (factorInputValues B W L columns)).map colC = factorInputValues B W L columns := by
  apply factorIntegerRows_colC
  intro row hr z hz
  exact (factorInputValues_format B W w L columns hlen hformat row hr z hz).1

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
