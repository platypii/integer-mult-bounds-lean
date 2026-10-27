module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorPageIntegers
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorRankStability
public import IntegerMultBounds.MathlibTM2.Fast.BandFactor

/-! Identify the emitted integer page and all its window-factor states with one band matrix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.SchurDominance

variable {s : ℕ} [NeZero s]

noncomputable def factorRankIntegerMatrix (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) : ℕ → ℕ → ℤ :=
  fun m n => (factorRankWord B W columns n m).re

theorem factorRankIntegerMatrix_out (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (m n : ℕ) (hout : B.card ≤ m ∨ B.card ≤ n) :
    factorRankIntegerMatrix B W columns m n = 0 := by
  have hv : ¬FactorRankValid B.card W n m := by
    intro h
    obtain ⟨hn,hm,_,_⟩ := h
    omega
  simp [factorRankIntegerMatrix,factorRankWord,hv]

theorem factorRankIntegerMatrix_value (A q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) :
    gvM q (factorRankIntegerMatrix B W columns) = factorRankMatrix A q w B W columns := by
  funext m n
  simpa only [gvM,gv,factorRankIntegerMatrix,value] using
    factorRankWord_value A q w B W n m columns hlen hformat hA hw

theorem factorWindowIntegers_windowZ (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) :
    factorIntegerRows (factorWindowValues B W columns) = windowZ W (factorRankIntegerMatrix B W columns) := by
  simp [factorIntegerRows,factorWindowValues,factorRowValues,windowZ,winRowZ,
    factorRankIntegerMatrix,List.map_map,Function.comp_def]

theorem factorInputIntegers_inputsZ (B : Finset (ZMod s)) (W L : ℕ)
    (columns : List (ZMod s → GaussianInt)) :
    factorIntegerRows (factorInputValues B W L columns) = inputsZ W (factorRankIntegerMatrix B W columns) L := by
  have hr : List.range' 1 L = (List.range' 0 L).map (1+·) := by
    simpa using (List.map_add_range' (a := 1) 0 L 1).symm
  simp [factorIntegerRows,factorInputValues,factorRowValues,inputsZ,winRowZ,
    factorRankIntegerMatrix,hr,List.map_map,Function.comp_def,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

theorem factorRankIntegerMatrix_band (A q w : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) :
    BandFrom W (gvM q (factorRankIntegerMatrix B W columns)) 0 := by
  rw [factorRankIntegerMatrix_value A q w B W columns hlen hformat hA hw]
  exact factorRankMatrix_band A q w B W columns

theorem factorIntegerState_window (A q w K : ℕ) (B : Finset (ZMod s)) (W : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat w columns) (hA : 4 ≤ A) (hw : 1 ≤ w) (hq : 2 ≤ q)
    (m : ℕ) (hm : m ≤ B.card) :
    facState q K (factorIntegerRows (factorWindowValues B W columns))
      (factorIntegerRows (factorInputValues B W B.card columns)) m =
      (List.range' m (W+1)).map (winRowZ W (stgZ q K (factorRankIntegerMatrix B W columns) m) m) := by
  rw [factorWindowIntegers_windowZ,factorInputIntegers_inputsZ]
  exact facState_window q K W hq _
    (factorRankIntegerMatrix_band A q w B W columns hlen hformat hA hw) B.card m hm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
