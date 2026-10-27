module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFoldedBandSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryBand
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputDecode

/-! The column-wise packed page and its decoded boundary-matrix contract. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {s : ℕ} [NeZero s]

noncomputable def bandColumnWords (A w : ℕ) (B : Finset (ZMod s)) (W n : ℕ)
    (C : ZMod s → GaussianInt) : List (Fin (A+4)) :=
  cstream A w ((foldedBandRows B W n).reverse.map C)

noncomputable def bandTableWords (A w : ℕ) (B : Finset (ZMod s)) (W : ℕ) :
    List (ZMod s → GaussianInt) → ℕ → List (Fin (A+4))
  | [], _ => []
  | C::columns, n => bandTableWords A w B W columns (n+1)++bandColumnWords A w B W n C

theorem bandTableWords_append (A w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (C : ZMod s → GaussianInt) (n : ℕ) :
    bandTableWords A w B W (columns++[C]) n =
      bandColumnWords A w B W (n+columns.length) C++bandTableWords A w B W columns n := by
  induction columns generalizing n with
  | nil => simp [bandTableWords]
  | cons D columns ih =>
      simp [bandTableWords,ih,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem bandTableWords_storage (A w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (n : ℕ) :
    (bandTableWords A w B W columns n).length ≤ columns.length*(2*W+1)*w := by
  induction columns generalizing n with
  | nil => simp [bandTableWords]
  | cons C columns ih =>
      have hc : (bandColumnWords A w B W n C).length ≤ (2*W+1)*w := by
        simpa [bandColumnWords,List.map_reverse] using foldedBandColumn_storage B W n A w C
      have hrest := ih (n+1)
      simp only [bandTableWords,List.length_append,List.length_cons]
      nlinarith only [hc,hrest]

noncomputable def columnWordRead (A q w : ℕ) (C : ZMod s → GaussianInt) (i : ZMod s) : ℝ :=
  (value q (decodeWord (csyms A w (C i)))).re


def ColumnFamilyAccurate (A q w : ℕ) (B : Finset (ZMod s))
    (S : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ) (columns : List (ZMod s → GaussianInt)) : Prop :=
  ∀ n (hn : n < columns.length), ∀ i ∈ B,
    |columnWordRead A q w columns[n] i-S i (bFoldAt s B n)| ≤ ε

theorem ColumnFamilyAccurate.append (A q w : ℕ) (B : Finset (ZMod s))
    (S : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ) (columns : List (ZMod s → GaussianInt))
    (C : ZMod s → GaussianInt) (hcolumns : ColumnFamilyAccurate A q w B S ε columns)
    (hC : ∀ i ∈ B, |columnWordRead A q w C i-S i (bFoldAt s B columns.length)| ≤ ε) :
    ColumnFamilyAccurate A q w B S ε (columns++[C]) := by
  intro n hn i hi
  by_cases h : n < columns.length
  · simpa only [List.getElem_append_left h] using hcolumns n h i hi
  · have heq : n = columns.length := by simp only [List.length_append,List.length_singleton] at hn; omega
    subst n
    simpa using hC i hi


def ColumnFamilyFormat (w : ℕ) (columns : List (ZMod s → GaussianInt)) : Prop :=
  ∀ C ∈ columns, (∀ i, (C i).im = 0) ∧ ∀ i, Fits w (C i)

theorem ColumnFamilyFormat.append (w : ℕ) (columns : List (ZMod s → GaussianInt))
    (C : ZMod s → GaussianInt) (hcolumns : ColumnFamilyFormat w columns)
    (hreal : ∀ i, (C i).im = 0) (hfit : ∀ i, Fits w (C i)) :
    ColumnFamilyFormat w (columns++[C]) := by
  intro D hD
  simp only [List.mem_append,List.mem_singleton] at hD
  rcases hD with hD | hD
  · exact hcolumns D hD
  · subst D; exact ⟨hreal,hfit⟩

noncomputable def computedBoundaryTable (A q w : ℕ) (B : Finset (ZMod s))
    (columns : List (ZMod s → GaussianInt)) : Matrix (ZMod s) (ZMod s) ℝ :=
  fun i j => if h : bFoldPos s B j < columns.length then
    columnWordRead A q w columns[bFoldPos s B j] i else 0

theorem computedBoundaryTable_error (A q w : ℕ) (B : Finset (ZMod s))
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (S : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ)
    (hcolumns : ∀ n (hn : n < columns.length), ∀ i ∈ B,
      |columnWordRead A q w columns[n] i-S i (bFoldAt s B n)| ≤ ε) :
    ∀ i ∈ B, ∀ j ∈ B, |computedBoundaryTable A q w B columns i j-S i j| ≤ ε := by
  intro i hi j hj
  have hn : bFoldPos s B j < columns.length := by rw [hlen]; exact bFoldPos_lt s B j hj
  simpa [computedBoundaryTable,hn,bFoldAt_bFoldPos s B j hj] using hcolumns (bFoldPos s B j) hn i hi

theorem computedBoundaryTable_band_error (A q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (S : Matrix (ZMod s) (ZMod s) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hsupport : ∀ i ∈ B, ∀ j ∈ B, S i j ≠ 0 → FoldBRel s B W i j)
    (hcolumns : ∀ n (hn : n < columns.length), ∀ i ∈ B,
      |columnWordRead A q w columns[n] i-S i (bFoldAt s B n)| ≤ ε) :
    ∀ i ∈ B, ∀ j ∈ B,
      |bandBoundaryTable B W (computedBoundaryTable A q w B columns) i j-S i j| ≤ ε :=
  bandBoundaryTable_error B W S _ ε hε hsupport
    (computedBoundaryTable_error A q w B columns hlen S ε hcolumns)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
