module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowField

/-! State coupling accuracy directly on the computed integer field after exact decoding. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem couplingRowField_error {A s t p u q w rhsExp inputExp countExp a b : ℕ}
    [NeZero s] {α d : ℝ} (boundary : Bool) (hA : 96 ≤ A) (hp : 0 < p) (hst : s < t)
    (hαu : α^2 = (u : ℝ)) (hθ : 0 < (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hw : q+couplingRowExponent rhsExp inputExp (8*p+1) countExp+2 ≤ w)
    (C B : ZMod s → GaussianInt) (x b₀ : ZMod s → ℝ) (K ε rhsError : ℝ) (hε : 0 ≤ ε)
    (hcount : 2*PhaseCellBand.width p u+1 ≤ 2^countExp)
    (hB : ∀ i, ‖value q (B i)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ i ∈ (if boundary then haloBoundary s t (PhaseCellBand.width p u) a b
        else haloInterior s t (PhaseCellBand.width p u) a b), ‖value q (C i)‖ ≤ (2 : ℝ)^inputExp)
    (hx : ∀ i ∈ (if boundary then haloBoundary s t (PhaseCellBand.width p u) a b
        else haloInterior s t (PhaseCellBand.width p u) a b), |(value q (C i)).re-x i| ≤ ε)
    (hmass : ∀ i < s, (((couplingOffsets (PhaseCellBand.width p u)).reverse).map (fun δ =>
      |(PhaseCellCrossCell.entry (2^15*p) s t u (PhaseCellBand.width p u) i (i+δ) : ℝ)|)).sum ≤ K)
    (hBError : ∀ i, |(value q (B i)).re-b₀ i| ≤ rhsError) :
    ∀ i, |(value q (couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b boundary C B i)).re-
      (b₀ i-SchurDominance.couple (realMatrix s t p u)
        (if boundary then haloBoundary s t (PhaseCellBand.width p u) a b
          else haloInterior s t (PhaseCellBand.width p u) a b) x i)| ≤
      (2*PhaseCellBand.width p u+1)*(2/(2 : ℝ)^q)+rhsError+
        (2*PhaseCellBand.width p u+1)*((2 : ℝ)^inputExp*(1/(2 : ℝ)^q))+K*ε := by
  intro i
  let z := couplingRowField (2^15*p) q t u (PhaseCellBand.width p u) a b boundary C B i
  have hn := couplingRowField_norm boundary hp hst hαu hθ hgap hbudget C B hcount hB hC i
  have hfit : Fits w z := fits_of_value_power (q := q)
    (e := couplingRowExponent rhsExp inputExp (8*p+1) countExp) hw z hn
  have hh := maskedCouplingRow_error (A := A) (s := s) (t := t) (p := p) (u := u)
    (q := q) (w := w) (rhsExp := rhsExp) (inputExp := inputExp) (countExp := countExp)
    (a := a) (b := b) (i := i.val) boundary hA hp hst hαu hθ hgap hbudget hw i.val_lt
    C x (B i) (b₀ i) K ε rhsError hε hcount (hB i) hC hx (hmass i.val i.val_lt) (hBError i) []
  dsimp only at hh
  have hz : B i-(List.zipWith (fun x c => tdivN q (x*c))
      (couplingInputWords boundary t (PhaseCellBand.width p u) a b i.val C)
      (couplingCoefficientWords (2^15*p) q s t u (PhaseCellBand.width p u) i.val)).sum = z := rfl
  rw [hz] at hh
  have htake : (csyms A w z).take w = csyms A w z := List.take_of_length_le (by simp)
  have hw0 : 1 ≤ w := by dsimp [couplingRowExponent] at hw; omega
  rw [List.append_nil,htake,decodeWord_of_fits (by omega) hw0 z hfit] at hh
  simpa only [ZMod.natCast_zmod_val] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
