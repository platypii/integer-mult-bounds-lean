module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrefixRelease
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Native certificates for consuming owned prefixes and dimension counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P₀ U : Type}

theorem releasePrefix_native (count src saved tmp : Fin T) :
    mnNativePushBound 2 (releasePrefix (P := P₀) (Q := Q) (A := A) (U := U) count src saved tmp) := by
  simp [releasePrefix,transfer,transferAct,scanR,drainR,popDo,keepIn,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem releaseFromDimensions_native {T : ℕ} (a b count src saved buf tmp : Fin T) :
    mnNativePushBound 3 (releaseFromDimensions (P := P₀) (Q := Q) (A := A) (U := U)
      a b count src saved buf tmp) := by
  simp [releaseFromDimensions,releasePrefix,unaryProduct,transfer,transferAct,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
