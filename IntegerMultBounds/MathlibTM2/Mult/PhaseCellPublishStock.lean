module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOutputRows
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Coordinate-order publication uses only native linear traffic. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem publishFromDimensions_native :
    mnNativePushBound 3 (publishFromDimensions (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [publishFromDimensions,halfCount,halfPairAct,publishRows,reverseRows,
    reverseRowLoopBody,reverseRowNext,reverseWords,reverseLoopBody,reverseNext,
    releaseFromDimensions,releasePrefix,clearWords,unaryProduct,
    copyPrefix,copyR,copyStep,transfer,transferAct,ucopy,umulSym,
    scanP,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush]

theorem publishWords_exec_within (M L w : ℕ) (xs : List GaussianInt) (hlen : xs.length = M * L)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R 108).length = 2 * M) (hrows : (S.R 103).length = L) (hwidth : (S.R 94).length = w)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (hclean : ∀ k ∈ [(1 : Fin 117), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 84], S.R k = [])
    (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ publishFromDimensionsCost M L w ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S) + depth +
        3 * publishFromDimensionsCost M L w) depth publishFromDimensions (mk v S) m
        (mk v' { S with R := Function.update S.R 93 (cstream A w (publishedWords M L xs) ++ tail) }) := by
  obtain ⟨v',m,hu,hm,he⟩ := publishWords_exec (body := body) M L w xs hlen
    v S tail hbatch hrows hwidth hsrc hclean
  exact ⟨v',m,hu,hm,mn_native_exec_within he 3 publishFromDimensions_native depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm) _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
