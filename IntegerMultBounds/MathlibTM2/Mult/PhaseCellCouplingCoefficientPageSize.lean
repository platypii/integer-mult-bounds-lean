module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientPageData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGuardedCouplingCost

/-! Exact sparse-page word counts and their geometry bound. This is retained page stock, not an execution peak. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem couplingCoefficientPage_length_sum (P q s t u band a b N : ℕ) :
    (couplingCoefficientPage P q s t u band a b N).length =
      (Finset.range N).sum (fun i => if couplingSkipAt true s t band a b i then 0 else 2*band+1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [couplingCoefficientPage_succ,List.length_append,couplingCoefficientPageChunk_length,
      Finset.sum_range_succ,ih]

theorem couplingCoefficientPage_length (P q s t u band a b N : ℕ) :
    (couplingCoefficientPage P q s t u band a b N).length =
      ((Finset.range N).filter (fun i => couplingSkipAt true s t band a b i ≠ true)).card*(2*band+1) := by
  rw [couplingCoefficientPage_length_sum,Finset.sum_ite]
  simp

theorem couplingCoefficientPage_length_le_geometry {s t : ℕ} [NeZero s] (hst : s < t)
    (P q u band a b : ℕ) (hb : b ≤ s) :
    (couplingCoefficientPage P q s t u band a b s).length ≤
      (haloBoundaryCountBound s t (2*band) a b+4*band)*(2*band+1) := by
  have hpart := Finset.card_filter_add_card_filter_not (s := Finset.range s)
    (fun i => couplingSkipAt true s t band a b i = true)
  have htrue := couplingGuard_true_count hst true band a b hb
  have hfalse : ((Finset.range s).filter (fun i => couplingSkipAt true s t band a b i ≠ true)).card =
      s-(couplingZeroRows true s t band a b).card := by
    have hsum : (couplingZeroRows true s t band a b).card+
        ((Finset.range s).filter (fun i => couplingSkipAt true s t band a b i ≠ true)).card = s := by
      simpa only [Finset.card_range,htrue] using hpart
    omega
  rw [couplingCoefficientPage_length,hfalse]
  exact Nat.mul_le_mul_right _ (couplingGuard_full_count_le hst true band a b)

theorem couplingCoefficientPage_symbols_le_geometry {s t A : ℕ} [NeZero s] (hst : s < t)
    (P q w u band a b : ℕ) (hb : b ≤ s) :
    (cstream A w (couplingCoefficientPage P q s t u band a b s)).length ≤
      (haloBoundaryCountBound s t (2*band) a b+4*band)*(2*band+1)*w := by
  simpa using Nat.mul_le_mul_right w (couplingCoefficientPage_length_le_geometry hst P q u band a b hb)

/-- The page prefix plus its generated unary word count and row-width metadata. -/
theorem couplingCoefficientPage_owned_size_le_geometry {s t A : ℕ} [NeZero s] (hst : s < t)
    (P q w u band a b : ℕ) (hb : b ≤ s) :
    (cstream A w (couplingCoefficientPage P q s t u band a b s)).length+
        (couplingCoefficientPage P q s t u band a b s).length+(2*band+1) ≤
      (haloBoundaryCountBound s t (2*band) a b+4*band)*(2*band+1)*(w+1)+(2*band+1) := by
  simpa [Nat.mul_add] using Nat.add_le_add_right
    (Nat.mul_le_mul_right (w+1) (couplingCoefficientPage_length_le_geometry hst P q u band a b hb)) (2*band+1)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
