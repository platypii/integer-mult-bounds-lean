module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Fast.TableVM
public import IntegerMultBounds.MathlibTM2.StackStockComposition
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders

/-! Export a narrow geometry header from a wider retained table word.
The counted-prefix copier restores its source and scratch verbatim. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem copyBinaryHeader_native (count src dst saved tmp : Fin T) : mnNativePushBound 3
    (copyPrefix (P := P) (Q := Q) (A := A) (U := U) count src dst saved tmp) := by
  simp [copyPrefix,transfer,transferAct,copyR,copyStep,moveR,moveStep,scanR,drainR,popDo,keepIn,
    whileR,peekR,mnNativePushBound,mnActPush]

/-- No numerical fit premise is needed: binSyms already denotes the low bits.
A caller using the header as a natural number separately proves x < 2^B. -/
theorem copyBinaryHeader_exec_within (body : P → Pr P T Q A U)
    (count src dst saved tmp : Fin T) (hreg : [count,src,dst,saved,tmp].Nodup)
    (B D x : ℕ) (hBD : B ≤ D) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = B) (hsrc : S.R src = binSyms D x)
    (hdst : S.R dst = []) (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*(10*B+10)) depth
        (copyPrefix count src dst saved tmp) (mk v S) (10*B+10)
        (mk v' {S with R := Function.update S.R dst (binSyms B x)}) := by
  have htake : (binSyms D x : List (Fin (A+4))).take B = binSyms B x := by
    have hh := tbl_take_binSyms (A := A) B (D-B) x
    simpa only [Nat.add_sub_of_le hBD] using hh
  obtain ⟨v',hu,he⟩ := copyPrefix_exec (body := body) hreg v S
    (binSyms B x) ((binSyms D x).drop B)
    (by rw [←htake,List.take_append_drop,hsrc])
    (by simpa only [length_binSyms] using hcount) hsaved htmp
  simp only [length_binSyms,hdst,List.append_nil] at he
  exact ⟨v',hu,mn_native_exec_within he 3 (copyBinaryHeader_native _ _ _ _ _) depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
