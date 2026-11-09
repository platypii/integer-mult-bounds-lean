module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareBatchGeneratorPage
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Generator replication pays only linear encoded traffic per additional batch cell. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem prepareBatchGeneratorPage_native :
    mnNativePushBound 8 (prepareBatchGeneratorPage (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [prepareBatchGeneratorPage,loadBatchHeader,gatherRead,gatherReadStep,WordCmd.peekRp,
    replicateGenerators,replicateGeneratorBanks,packRepeatedGenerators,repeatPrefix,
    copyAfterPrefix,takePrefix,releasePrefix,clearWords,unaryProduct,transfer,transferAct,
    copyPrefix,copyR,copyStep,umul,uadd,ucopy,umulSym,scanP,scanR,drainR,popDo,
    keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]

def prepareBatchGeneratorPageWorkspace (B L q : ℕ) : ℕ :=
  8*prepareBatchGeneratorPageCost B L q

/-- Every extra cell contributes a linear copy/packing allowance, without numerical scratch. -/
theorem prepareBatchGeneratorPageWorkspace_affine (B L q : ℕ) :
    prepareBatchGeneratorPageWorkspace B L q = prepareBatchGeneratorPageWorkspace 0 L q+
      B*(8*(38*(L*(2*q+8))+43)) := by
  simp only [prepareBatchGeneratorPageWorkspace,prepareBatchGeneratorPageCost,replicateGeneratorsCost]
  ring

theorem prepareBatchGeneratorPage_exec_within (B P s t u band L q n : ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (controlTail tail : List (Fin (A + 4)))
    (hL : (S.R 103).length = L) (hq : (S.R 112).length = q)
    (hcontrol : S.R 109 = List.replicate B tick ++ blank :: controlTail)
    (hsrc : S.R 110 = generatorPage A P s t u band L q n ++ tail)
    (hfresh : ∀ k ∈ [(94 : Fin 117), 96, 97, 98, 99, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareBatchGeneratorPageCost B L q ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+prepareBatchGeneratorPageWorkspace B L q)
        depth prepareBatchGeneratorPage (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update (Function.update S.R
          109 controlTail) 96 (List.replicate B tick)) 94 (List.replicate (2 * q + 8) tick))
          110 (batchGeneratorPage A B P s t u band L q n ++ tail)) })) := by
  obtain ⟨v',m,hu,hm,he⟩ := prepareBatchGeneratorPage_exec (body := body)
    B P s t u band L q n v S controlTail tail hL hq hcontrol hsrc hfresh
  refine ⟨v',m,hu,hm,?_⟩
  intro depth
  exact mn_native_exec_within he 8 prepareBatchGeneratorPage_native depth _ (by
    unfold prepareBatchGeneratorPageWorkspace
    omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
