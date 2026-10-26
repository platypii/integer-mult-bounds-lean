module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowValue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedCouplingRowError

/-! Reuse a computed row-pass output as an ambient integer field. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

def couplingRowField {s : ℕ} [NeZero s] (P q t u band a b : ℕ) (boundary : Bool)
    (C B : ZMod s → GaussianInt) (i : ZMod s) : GaussianInt :=
  couplingRowWord P q t u band a b i.val boundary C (B i)

theorem couplingRowWords_eq_chirpLine {s : ℕ} [NeZero s] (P q t u band a b : ℕ)
    (boundary : Bool) (C B : ZMod s → GaussianInt) :
    couplingRowWords P q t u band a b boundary C 0 (chirpLine s B) =
      chirpLine s (couplingRowField P q t u band a b boundary C B) := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  have hjs : j < s := by simpa using hj
  rw [couplingRowWords_getElem P q t u band a b 0 boundary C (chirpLine s B) j (by simpa using hjs)]
  simp [chirpLine,couplingRowField,Nat.mod_eq_of_lt hjs]

theorem couplingRowField_norm {s t p u q band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (boundary : Bool) (hp : 0 < p) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (C B : ZMod s → GaussianInt) (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ j, ‖value q (B j)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ (if boundary then PhaseCellDiscreteGeometry.haloBoundary s t band a b
        else PhaseCellDiscreteGeometry.haloInterior s t band a b), ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (i : ZMod s) :
    ‖value q (couplingRowField (2^15*p) q t u band a b boundary C B i)‖ ≤
      (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp := by
  exact fixedPointRow_norm q rhsExp inputExp (8*p+1) countExp (B i)
    (couplingInputWords boundary t band a b i.val C) (couplingCoefficientWords (2^15*p) q s t u band i.val)
    (by simp) (by simpa using hcount) (hB i) (couplingInputWords_norm boundary t band a b i.val C hC)
    (fun z hz => (couplingCoefficientWords_bounds hp (NeZero.pos s) hst hαu hθ hgap hbudget z hz).1)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
