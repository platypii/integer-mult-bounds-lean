module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRowValues

/-! The complete factor-input layout: an initial window followed by shifted update rows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.SchurDominance

variable {s : ℕ} [NeZero s]

noncomputable def factorWindowValues (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) : List (List GaussianInt) :=
  (List.range' 0 (W+1)).map (fun m => factorRowValues B W 0 m columns)

noncomputable def factorInputValues (B : Finset (ZMod s)) (W L : ℕ)
    (columns : List (ZMod s → GaussianInt)) : List (List GaussianInt) :=
  (List.range' 1 L).map (fun n => factorRowValues B W n (W+n) columns)

@[simp] theorem factorWindowValues_length (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) : (factorWindowValues B W columns).length = W+1 := by
  simp [factorWindowValues]

@[simp] theorem factorInputValues_length (B : Finset (ZMod s)) (W L : ℕ)
    (columns : List (ZMod s → GaussianInt)) : (factorInputValues B W L columns).length = L := by
  simp [factorInputValues]

theorem factorWindowValues_row_length (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) :
    ∀ row ∈ factorWindowValues B W columns, row.length = 2*W+1 := by
  intro row hr
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hr
  exact factorRowValues_length B W 0 m columns

theorem factorInputValues_row_length (B : Finset (ZMod s)) (W L : ℕ)
    (columns : List (ZMod s → GaussianInt)) :
    ∀ row ∈ factorInputValues B W L columns, row.length = 2*W+1 := by
  intro row hr
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hr
  exact factorRowValues_length B W n (W+n) columns

theorem factorWindowValues_grid (A q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) :
    (factorWindowValues B W columns).map (List.map (fun z => (value q z).re)) =
      window W (factorRankMatrix A q w B W columns) 0 := by
  simp only [factorWindowValues,List.map_map,window]
  apply List.map_congr_left
  intro m _
  exact factorRowValues_grid A q w B W 0 m columns hlen hformat hA hw

theorem factorInputValues_grid (A q w : ℕ) (B : Finset (ZMod s)) (W L : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) :
    (factorInputValues B W L columns).map (List.map (fun z => (value q z).re)) =
      (List.range' 1 L).map (fun n => winRow W (factorRankMatrix A q w B W columns) n (W+n)) := by
  simp only [factorInputValues,List.map_map]
  apply List.map_congr_left
  intro n _
  exact factorRowValues_grid A q w B W n (W+n) columns hlen hformat hA hw

theorem factorWindowValues_format (B : Finset (ZMod s)) (W w : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) :
    ∀ row ∈ factorWindowValues B W columns, ∀ z ∈ row, z.im = 0 ∧ Fits w z := by
  intro row hr
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hr
  exact factorRowValues_format B W w 0 m columns hlen hformat

theorem factorInputValues_format (B : Finset (ZMod s)) (W w L : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) :
    ∀ row ∈ factorInputValues B W L columns, ∀ z ∈ row, z.im = 0 ∧ Fits w z := by
  intro row hr
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hr
  exact factorRowValues_format B W w n (W+n) columns hlen hformat

private theorem flatten_length_of_rows (rows : List (List GaussianInt)) (d : ℕ)
    (hrows : ∀ row ∈ rows, row.length = d) : rows.flatten.length = rows.length*d := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr := hrows row (by simp)
    have hs : ∀ r ∈ rows, r.length = d := fun r h => hrows r (by simp [h])
    simp [hr,ih hs,Nat.add_mul,Nat.add_comm]

theorem factorPageValues_length (B : Finset (ZMod s)) (W L : ℕ)
    (columns : List (ZMod s → GaussianInt)) :
    ((factorWindowValues B W columns).flatten++(factorInputValues B W L columns).flatten).length =
      (W+1+L)*(2*W+1) := by
  rw [List.length_append,flatten_length_of_rows _ _ (factorWindowValues_row_length B W columns),
    flatten_length_of_rows _ _ (factorInputValues_row_length B W L columns)]
  simp [Nat.add_mul]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
