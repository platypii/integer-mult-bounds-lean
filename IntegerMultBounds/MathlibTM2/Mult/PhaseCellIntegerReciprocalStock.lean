module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerReciprocal
public import IntegerMultBounds.MathlibTM2.StackResources

/-! One scalar reciprocal reserve is shared by the complete inverse setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellIntegerGenerators
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem generateReciprocal_native :
    mnNativePushBound 8 (generateReciprocal (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [generateReciprocal,generateReciprocalNumerator,divideRealWords,copyRealBits,
    cropReciprocal,generateSeed,seedBit,bdivmod,divIter,pushBit,
    bcopy,bzero,bclear,bshift,bpad1,bmoveLow,zipPass,zipInit,zipStep,
    eachSym,zeroBits,
    unaryProduct,copyPrefix,copyR,copyStep,takePrefix,transfer,transferAct,clearWords,
    umul,uadd,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,dropTop,
    moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

/-- A conservative single-division allowance, independent of row, iteration and batch counts. -/
def integerReciprocalWorkspace (q W : ℕ) : ℕ :=
  8*(W*(12*W+128)+6*(2*q+8)+4*q+134)

theorem generateIntegerReciprocal_exec_within {P s t u band L n q W : ℕ}
    (hA : 4 ≤ A) (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hL : 0 < L) (hn : 1 ≤ n) (hd : q + P * n < W) (hw : 2 * q + 8 ≤ W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tailX tailF : List (Fin (A + 4)))
    (hctx : IntegerGeneratorContext P s t u band L n W tailX tailF S)
    (hq : (S.R 112).length = q) :
    ∃ v' m, v'.user = v.user ∧ m ≤ W * (12 * W + 128) + 6 * (2 * q + 8) + 4 * q + 134 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+integerReciprocalWorkspace q W)
        depth generateReciprocal (mk v S) m
        (mk v' { S with R := Function.update S.R 96 (csyms A (2 * q + 8) (reciprocalWord P s t u band L q n)) }) ) := by
  obtain ⟨v',m,hu,hm,he⟩ := generateIntegerReciprocal_exec (body := body)
    hA hP hs hst hu hL hn hd hw v S tailX tailF hctx hq
  refine ⟨v',m,hu,hm,?_⟩
  intro depth
  exact mn_native_exec_within he 8 generateReciprocal_native depth _ (by
    unfold integerReciprocalWorkspace
    omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
