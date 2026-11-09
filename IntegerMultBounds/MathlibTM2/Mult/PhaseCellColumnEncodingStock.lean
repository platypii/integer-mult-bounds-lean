module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellColumnEncoding
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Encoding the retained integer column is linear native bit-slice traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.ToeplitzInverse
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem generateColumnEncoding_native :
    mnNativePushBound 8 (generateColumnEncoding (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [generateColumnEncoding,prepareColumnEncoding,encodeDyadicColumn,topPass,topWords,
    floorSliceWord,unaryProduct,usub,umul,dropTop,copyPrefix,copyR,copyStep,transfer,transferAct,
    clearWords,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

def columnEncodingWorkspace (L q W : ℕ) : ℕ :=
  8*(L*(20*W+6*(2*q+8)+23)+31*W+57)

theorem generateColumnEncoding_exec_within (P s t u band L n q W : ℕ) (hn : 1 ≤ n)
    (hscale : P * n + 1 ≤ W) (hqr : q ≤ P * n + 1)
    (hwidth : P * n + 1 - q + (2 * q + 8) ≤ W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX : List (Fin (A + 4)))
    (hrows : (S.R 102).length = L) (hW : (S.R 94).length = W)
    (hP : (S.R 114).length = P) (hnR : (S.R 116).length = n) (hq : (S.R 112).length = q)
    (hsrc : S.R 110 = cstream A W (rowColumnWords P s t u band L n) ++ tailX)
    (hfresh : ∀ k ∈ [(115 : Fin 117), 98, 107, 99, 104, 105, 113, 96], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ L * (20 * W + 6 * (2 * q + 8) + 23) + 31 * W + 57 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+columnEncodingWorkspace L q W)
        depth generateColumnEncoding (mk v S) m
        (mk v' { S with R := (Function.update S.R 111
          (cstream A (2 * q + 8) (columnWords P s t u band L q n) ++ S.R 111)) }) ) := by
  obtain ⟨v',m,hu,hm,he⟩ := generateColumnEncoding_exec (body := body)
    P s t u band L n q W hn hscale hqr hwidth v S tailX hrows hW hP hnR hq hsrc hfresh
  refine ⟨v',m,hu,hm,?_⟩
  intro depth
  exact mn_native_exec_within he 8 generateColumnEncoding_native depth _ (by
    unfold columnEncodingWorkspace
    omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
