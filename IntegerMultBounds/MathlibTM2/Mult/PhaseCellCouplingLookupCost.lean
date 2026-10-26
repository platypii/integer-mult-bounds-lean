module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCouplingLookup

/-! One paid query envelope is uniform over all retained signed offsets. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellRationalArgs

def couplingLookupRowCost (P q w s t u band a b i : ℕ) : ℕ :=
  let V := liftedCoefficientWidth P q w s t u band
  generateLiftedCoefficientWidthCost P q w s t u band+
    ((104*V+137)+((s+band+i+band)*(4*V+10)+24*V+41)+
      (6*tblC V V+64*V+65)+(6*s+19*V+14))+
    haloLookupFromHeadersCost V w s t band a b s+(2*(s+V)+5)

theorem closedCouplingLookupCost_le (negative : Bool) (P q w s t u band a b i d : ℕ)
    (hs : 0 < s) (hd : d ≤ band) :
    closedCouplingLookupCost negative P q w s t u band a b i d ≤
      couplingLookupRowCost P q w s t u band a b i := by
  have hk := (couplingIndex_lt (band := band) (i := i) (d := d) negative hs).le
  have hload := Nat.mul_le_mul_right (4*liftedCoefficientWidth P q w s t u band+10)
    (show s+band+i+d ≤ s+band+i+band by omega)
  have hlookup := Nat.mul_le_mul_right (4*liftedCoefficientWidth P q w s t u band+10)
    (show s+t+band+couplingIndex negative s band i d+a+b ≤ s+t+band+s+a+b by omega)
  have hseek := Nat.mul_le_mul_right (12*w+9) hk
  dsimp only [closedCouplingLookupCost,couplingLookupRowCost,couplingIndexFromHeadersCost,
    haloLookupFromHeadersCost,maskedHaloLookupCost]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
