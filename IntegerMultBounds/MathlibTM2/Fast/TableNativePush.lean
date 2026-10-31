module

public import IntegerMultBounds.MathlibTM2.Fast.TableVM
public import IntegerMultBounds.MathlibTM2.StackResources

/-! A structural push certificate for every compiled table program. The bound
is independent of table size, register placement and the concrete controller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.TableVM
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Node
variable {T Q A n : ℕ} {P U : Type}

private theorem tblInsProg_native (rg : TblR n → Fin T) (i : TblIns n) :
    mnNativePushBound 3 (tblInsProg (P := P) (Q := Q) (A := A) (U := U) rg i) := by
  cases i <;>
    simp [tblInsProg,tblLoad,tblClr01,tblStoreF,tblStoreR,tblDivCore,tblEmitStep,
      badd,bsub,bmul,bdivmod,bcopy,bzero,bclear,beq,baddTo,bshift,bpad1,bmoveLow,bpad,umulSym,dropTop,
      mulIter,divIter,pushBit,zipKeep,zipPass,zipInit,zipStep,eachSym,zeroBits,
      countIter,incrField,incStep,setCarry,moveR,moveStep,scanP,
      scanR,whileR,popPush,uclear,drainR,popDo,keepIn,pushN,peekR,
      mnNativePushBound,mnActPush]

private theorem tblTest_native (rg : TblR n → Fin T) (a b : Fin n) :
    mnNativePushBound 3 (tblTest (P := P) (Q := Q) (A := A) (U := U) rg a b) := by
  simp [tblTest,tblLoad,tblClr01,bcopy,bclear,blt,zipKeep,zipPass,zipInit,zipStep,
    moveR,moveStep,scanR,whileR,uclear,drainR,popDo,
    keepIn,pushN,peekR,mnNativePushBound,mnActPush]

theorem tblCompile_native (rg : TblR n → Fin T) (code : TblCode n) :
    mnNativePushBound 3 (tblCompile (P := P) (Q := Q) (A := A) (U := U) rg code) := by
  induction code with
  | ins i => exact tblInsProg_native rg i
  | seq c d hc hd => exact ⟨hc,hd⟩
  | ite a b c d hc hd => exact ⟨tblTest_native rg a b,hc,hd⟩
  | loop a b c hc => exact ⟨tblTest_native rg a b,hc,tblTest_native rg a b⟩

end IntegerMultBounds.MathlibTM2.Fast.TableVM
