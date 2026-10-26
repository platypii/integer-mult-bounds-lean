module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellKeyRuntimeFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOuterHeaders

/-! Caller key-runtime installation commutes with private halo header copies. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem initializedKeyRuntimeR_copiedHaloGroupR {A : ℕ} (R : Regs 144 A)
    (P N q l s t u band a b L V w K : ℕ) (keys : List (Fin (A+4))) :
    initializedKeyRuntimeR (copiedHaloGroupR P N q l s t u band a b L R) V w K keys =
      copiedHaloGroupR P N q l s t u band a b L (initializedKeyRuntimeR R V w K keys) := by
  funext k
  by_cases h111 : k = 111
  · subst k; simp [copiedHaloGroupR,initializedKeyRuntimeR]
  by_cases h113 : k = 113
  · subst k; simp [copiedHaloGroupR,initializedKeyRuntimeR]
  have hh := congrArg (fun R : Regs 144 A => R k)
    (initializedKeyRuntimeR_copiedGroupR R P N q l s t u band L V w K keys)
  simpa [copiedHaloGroupR,initializedKeyRuntimeR,Function.update_apply,h111,h113] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
