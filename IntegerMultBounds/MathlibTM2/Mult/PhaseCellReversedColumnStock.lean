module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReversedColumn
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Shifted reversal pays linear native traffic and preserves the first runtime column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem generateReversedColumn_native :
    mnNativePushBound 8 (generateReversedColumn (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [generateReversedColumn,shiftReverse,reverseWords,reverseLoopBody,reverseNext,
    copyPrefix,copyR,copyStep,transfer,transferAct,clearWords,umul,
    ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

def reversedColumnWorkspace (L q : ℕ) : ℕ :=
  8*((L-1)*(16*(2*q+8)+21)+4*L+12*(2*q+8)+4*q+31)

theorem generateReversedColumn_exec_within {P s t u band L q n : ℕ} (hL : 0 < L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hq : (S.R 112).length = q) (hrows : (S.R 102).length = L)
    (hsrc : S.R 111 = cstream A (2 * q + 8) (columnWords P s t u band L q n) ++ tail)
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106, 107], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+reversedColumnWorkspace L q)
        depth generateReversedColumn (mk v S)
        ((L - 1) * (16 * (2 * q + 8) + 21) + 4 * L + 12 * (2 * q + 8) + 4 * q + 31)
        (mk v' { S with R := (Function.update S.R 113
          (cstream A (2 * q + 8) (reversedColumnWords P s t u band L q n) ++ S.R 113)) }) ) := by
  obtain ⟨v',hu,he⟩ := generateReversedColumn_exec (body := body) hL v S tail hq hrows hsrc hfresh
  exact ⟨v',hu,fun depth => mn_native_exec_within he 8 generateReversedColumn_native depth _ (by
    unfold reversedColumnWorkspace
    omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
