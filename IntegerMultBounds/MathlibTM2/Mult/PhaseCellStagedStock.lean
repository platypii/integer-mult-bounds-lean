module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSizedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPayloadBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStagedExecution

/-! Complete cell workspace from empty owned buffers and a preserved payload. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.Main

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem stagePayload_native :
    mnNativePushBound 3 (stagePayload (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [stagePayload,fetchPage,pageAddress,copyRepeated,branchWords,halfCount,halfPairAct,
    unaryProduct,copyAfterPrefix,copyPrefix,copyR,copyStep,transfer,transferAct,clearWords,
    ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,
    uclear,mnNativePushBound,mnActPush]

def stagedCellWorkspace (R K q cExp e l w M L : ℕ) : ℕ :=
  3 * stagePayloadCost M L w + publishedCellWorkspace R K q cExp e l w M L

theorem stagedCell_sized_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l M L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s ≤ t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L)
    (hpad : L + L ≤ 2 ^ l + 1) (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < M, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ K) (depth : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let precision := 2 ^ 15 * p
    let band := PhaseCellBand.width p u
    let X : ℕ → List GaussianInt := fun _ => columnWords precision s t u band L q (j + 2)
    let Z : ℕ → List GaussianInt := fun _ => reversedColumnWords precision s t u band L q (j + 2)
    let a := reciprocalWord precision s t u band L q (j + 2)
    let source := (List.range M).flatMap (cellSourceRows L lo C)
    let factors := reciprocalWeightWords q ((List.range M).flatMap (cellWeightRows s t p u L lo))
    let payload := cstream A w source ++ (cstream A w factors ++ borrowed)
    let tailX := csyms A w a ++ (cstream A w (outputWeightWords q (executedOutputTable s t p u M L lo)) ++ payload)
    let S := inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (publishedWords M L (executedOutputWords s t p u q l M L j cExp lo C)) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧
      m ≤ stagePayloadCost M L w + cellArithmeticCost q (inputExponent p cExp) cExp (8 * p + 1) l w M L + publishFromDimensionsCost M L w ∧
      ExecWithin body (fun level z => mnSize z + level ≤
        mnSize (mk v (inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out)) + depth +
          stagedCellWorkspace R K q cExp (8 * p + 1) l w M L)
        depth (stagedCell hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out))
        m (mk v' SF) := by
  dsimp only
  obtain ⟨vf,nf,huf,hnf,hef,_⟩ := stagedCell_sized_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hpad lo C hC v tail borrowed inp out
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let source := (List.range M).flatMap (cellSourceRows L lo C)
  let factors := reciprocalWeightWords q ((List.range M).flatMap (cellWeightRows s t p u L lo))
  let payload := cstream A w source ++ (cstream A w factors ++ borrowed)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := stagePayloadBank_exec (body := body) q l w M L
    (fun _ => columnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (fun _ => reversedColumnWords (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (by intro n hn; simp) (by intro n hn; simp)
    (reciprocalWord (2 ^ 15 * p) s t u (PhaseCellBand.width p u) L q (j + 2))
    (outputWeightWords q (executedOutputTable s t p u M L lo)) source factors
    (by simp [outputWeightWords, executedOutputTable])
    (by simp [source, List.length_flatMap, cellSourceRows])
    (by simp [factors, reciprocalWeightWords, List.length_flatMap, cellWeightRows])
    v tail borrowed inp out
  have ht₁ := mn_native_exec_within he₁ 3 stagePayload_native depth
    (_ + depth + 3 * stagePayloadCost M L w)
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hm₁) _)
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := publishedCell_sized_exec_within (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hpad lo C hC v₁ tail payload inp out R K hpushR hpushK depth
  have ht := mn_seq_within_add ht₁ he₂
  obtain ⟨heqn,heqF⟩ := ht.toExec.unique hef
  rw [heqn,heqF] at ht
  exact ⟨vf,nf,huf,hnf,ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
