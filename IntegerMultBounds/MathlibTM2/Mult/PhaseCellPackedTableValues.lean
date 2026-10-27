module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryTable

/-! Structural word-level layout of the emitted packed table. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix

variable {s : ℕ} [NeZero s]

noncomputable def bandColumnValues (B : Finset (ZMod s)) (W n : ℕ) (C : ZMod s → GaussianInt) : List GaussianInt :=
  (foldedBandRows B W n).reverse.map C

noncomputable def bandTableValues (B : Finset (ZMod s)) (W : ℕ) :
    List (ZMod s → GaussianInt) → ℕ → List GaussianInt
  | [], _ => []
  | C::columns, n => bandTableValues B W columns (n+1)++bandColumnValues B W n C

theorem bandTableWords_values (A w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (n : ℕ) :
    bandTableWords A w B W columns n = cstream A w (bandTableValues B W columns n) := by
  induction columns generalizing n with
  | nil => simp [bandTableWords,bandTableValues]
  | cons C columns ih => simp [bandTableWords,bandTableValues,bandColumnValues,bandColumnWords,ih]

theorem bandTableValues_append (B : Finset (ZMod s)) (W : ℕ)
    (xs ys : List (ZMod s → GaussianInt)) (n : ℕ) :
    bandTableValues B W (xs++ys) n =
      bandTableValues B W ys (n+xs.length)++bandTableValues B W xs n := by
  induction xs generalizing n with
  | nil => simp [bandTableValues]
  | cons C xs ih =>
      simp [bandTableValues,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem bandTableValues_column (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (n : ℕ) (hn : n < columns.length) :
    bandTableValues B W columns 0 =
      bandTableValues B W (columns.drop (n+1)) (n+1)++
        bandColumnValues B W n columns[n]++bandTableValues B W (columns.take n) 0 := by
  have hs : columns.take n++[columns[n]]++columns.drop (n+1) = columns := by
    simpa only [List.take_one_drop_eq_of_lt_length hn,List.get_eq_getElem,List.drop_drop,Nat.add_comm 1]
      using IntegerMultBounds.MathlibTM2.Mult.ShortConv.slice_split columns n 1
  conv_lhs => rw [← hs]
  rw [bandTableValues_append,bandTableValues_append]
  simp [bandTableValues,List.length_take,Nat.min_eq_left hn.le,Nat.min_eq_left (show n+1 ≤ columns.length by omega),List.append_assoc]


/-- Count packed words structurally from dimensions, without inspecting coefficients. -/
def packedBandWordCount (rowCount W : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | L+1, n => packedBandWordCount rowCount W L (n+1)+(min rowCount (n+W+1)-(n-W))

theorem bandTableValues_length (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (n : ℕ) :
    (bandTableValues B W columns n).length = packedBandWordCount B.card W columns.length n := by
  induction columns generalizing n with
  | nil => rfl
  | cons C columns ih =>
      simp [bandTableValues,packedBandWordCount,bandColumnValues,foldedBandRows,foldedBandIndices,ih]

theorem bandTableValues_length_le (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (n : ℕ) :
    (bandTableValues B W columns n).length ≤ columns.length*(2*W+1) := by
  induction columns generalizing n with
  | nil => simp [bandTableValues]
  | cons C columns ih =>
      have hc : (bandColumnValues B W n C).length ≤ 2*W+1 := by
        simpa [bandColumnValues] using foldedBandRows_length_le B W n
      have hh := ih (n+1)
      simp only [bandTableValues,List.length_append,List.length_cons]
      nlinarith only [hc,hh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
