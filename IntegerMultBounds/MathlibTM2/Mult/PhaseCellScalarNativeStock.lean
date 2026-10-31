module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarFinish
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBankLoadStock
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopiesStock
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush

/-! Scalar routing, shared counter preparation and cleanup use native traffic.
The numerical stream has its own shared-reserve certificate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type}

theorem route_native : mnNativePushBound 3 (route (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [route,branchWords,halfCount,halfPairAct,takeFromWords,takePrefix,unaryProduct,
    copyPrefix,copyR,copyStep,transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,
    popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

theorem finish_native : mnNativePushBound 3 (finish (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [finish,moveR,moveStep,whileR,peekR,uclear,drainR,popDo,mnNativePushBound,mnActPush]

theorem prepare_native : mnNativePushBound 3 (prepare (P := P) (Q := Q) (A := A) (U := U)) := by
  change mnNativePushBound 3 (.seq (.seq (.seq unarySetup (chirpBankLoad bank bankInput 23 23))
    (chirpMultiplierSetup bank cr)) (clearWords setupPorts))
  refine ⟨⟨⟨?_,chirpBankLoad_native _ _ _ _⟩,?_⟩,clearWords_native_three setupPorts⟩
  · simp [unarySetup,toBinary,bzero,zeroBits,popPush,eachSym,countIter,incrField,incStep,setCarry,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · exact ⟨tblCompile_native _ _,tblUnaryCopies_native _ _,tblCompile_native _ _⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
