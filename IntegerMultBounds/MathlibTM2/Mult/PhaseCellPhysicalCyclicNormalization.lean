module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicNormalizationWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicRounding

/-! Shared physical rounding ports and cost. Narrow executor: restore commit 4c755426. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def cyclicRoundPorts : Fin 4 → Fin 280 := ![269,270,271,272]

theorem cyclicRoundPorts_injective : Function.Injective cyclicRoundPorts := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cyclicRoundPorts]

def physicalCyclicNormalizationCost (p q a n : ℕ) : ℕ :=
  let P₀ := 2^15*p
  let B := cyclicNormalizationWidth P₀ q
  (19*P₀+19*q+17)+(8*q+4*(2*a+n)+21)+
    ((1+(P₀+q)*(4*B+10)+2*(8*B+12))+25*(4*B+4)+2*(8*B+8)+2+
      (18+(4*Nat.size (4*p)+31))*tblC B 0+
      roundPackedKeyCost B (2*q+8) (2*p+13) n (2*q+8) n+(2*(25*B)+2*25+1))+
    (2*((2*q+8)+n+B)+7)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
