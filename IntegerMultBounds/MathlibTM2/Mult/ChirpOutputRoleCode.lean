module

public import IntegerMultBounds.MathlibTM2.Fast.CMulRegs

/-! # Shared finite encoding of the thirty complex multiplier roles -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.OutputPlacement

open IntegerMultBounds.MathlibTM2.Fast

def code : CR → Fin 30
  | .xs => 0 | .ys => 1 | .xsv => 2 | .ysv => 3 | .acc => 4 | .out => 5
  | .wn => 6 | .pn => 7 | .nn => 8 | .tmp => 9
  | .u0 => 10 | .u1 => 11 | .u2 => 12 | .u3 => 13
  | .ma => 14 | .mb => 15 | .mc => 16 | .md => 17
  | .sa => 18 | .sb => 19 | .sc => 20 | .sd => 21
  | .p1 => 22 | .p2 => 23 | .p3 => 24 | .p4 => 25
  | .qr => 26 | .qi => 27 | .sr => 28 | .si => 29

theorem code_injective : Function.Injective code := by
  intro r s h
  cases r <;> cases s <;> simp_all [code]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.OutputPlacement
