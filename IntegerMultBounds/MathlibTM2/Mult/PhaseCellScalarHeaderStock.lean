module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallUnaryScalarInputs
public import IntegerMultBounds.MathlibTM2.Mult.ChirpMultiplierSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopiesStock
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Structural native-work bounds for ordinary scalar loading and header setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

private theorem zero_bank_native (width tmp : Fin T) (rs : List (Fin T)) :
    mnNativePushBound 3 (zeroWordBank (P := P) (Q := Q) (A := A) (U := U) width tmp rs) := by
  induction rs with
  | nil => simp [zeroWordBank,mnNativePushBound,mnActPush]
  | cons r rs ih =>
    simp [zeroWordBank,ih,bzero,zeroBits,umulSym,scanR,drainR,popDo,keepIn,pushN,
      moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

private theorem load_headers_native {n : ℕ} (rg : TblR n → Fin T) (src : Fin T) (rs : List (Fin n)) :
    mnNativePushBound 3 (loadBinaryHeaders (P := P) (Q := Q) (A := A) (U := U) rg src rs) := by
  induction rs with
  | nil => simp [loadBinaryHeaders,mnNativePushBound,mnActPush]
  | cons r rs ih =>
    simp [loadBinaryHeaders,loadBinaryHeader,ih,takePrefix,transfer,transferAct,
      moveR,moveStep,uclear,scanR,drainR,popDo,keepIn,whileR,peekR,mnNativePushBound,mnActPush]

theorem binaryHeaderQueue_native (width word saved tmp dst carry : Fin T) (ports : List (Fin T)) :
    mnNativePushBound 3 (binaryHeaderQueue (P := P) (Q := Q) (A := A) (U := U) width word saved tmp dst carry ports) := by
  induction ports with
  | nil => simp [binaryHeaderQueue,mnNativePushBound,mnActPush]
  | cons src ports ih =>
    simp [binaryHeaderQueue,ih,prependBinaryHeader,toBinary,bzero,zeroBits,eachSym,countIter,incrField,
      incStep,setCarry,moveRightOrdered,moveR,moveStep,umulSym,scanR,drainR,popDo,keepIn,pushN,
      popPush,whileR,peekR,mnNativePushBound,mnActPush]

theorem installUnaryScalarInputs_native {n : ℕ} (rg : TblR n → Fin T)
    (header word saved tmp carry : Fin T) (ports : List (Fin n × Fin T)) :
    mnNativePushBound 3 (installUnaryScalarInputs (P := P) (Q := Q) (A := A) (U := U)
      rg header word saved tmp carry ports) := by
  exact ⟨binaryHeaderQueue_native ..,zero_bank_native ..,load_headers_native ..⟩

theorem chirpMultiplierSetup_native (rg : TblR 5 → Fin T) (cr : CR → Fin T) :
    mnNativePushBound 3 (chirpMultiplierSetup (P := P) (Q := Q) (A := A) (U := U) rg cr) :=
  ⟨tblCompile_native ..,mnNativePushBound_mono (by decide) (tblUnaryCopies_native ..),tblCompile_native ..⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
