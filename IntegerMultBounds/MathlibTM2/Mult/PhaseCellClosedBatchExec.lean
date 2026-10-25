module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBatchRuntime

/-! A fully cleaned sized batch execution, with the entire setup, arithmetic,
publication and release time ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

noncomputable def closedBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 117 Q A U :=
  .seq (generatedBatch hR hQ) releaseBatchRuntime

def sizedClosedBatchCost (p l B L s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  generatedBatchSetupCost (2^15*p) (j+1) q s t u (PhaseCellBand.width p u) l L B +
    stagePayloadCost B L w + cellArithmeticCost q (inputExponent p cExp) cExp (8*p+1) l w B L +
    publishFromDimensionsCost B L w + releaseBatchRuntimeCost B L q l

theorem closedBatch_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
    ∃ v' m, v'.user = v.user ∧ m ≤ sizedClosedBatchCost p l B L s t u target rhsExp ∧
      Exec body (closedBatch hR hQ)
        (mk v (batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B (fun n => (lo n).val)
          rhs borrowed tail inp out)) m
        (mk v' (releasedCellBank rhs borrowed
          (cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C)) ++ tail) inp out)) ∧
      ∀ n : Fin B, (executedRun s t p u q l w B L j cExp lo C n tail).Valid s t p u (lo n) L
        (fun k => (value q (C n k)).re) (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let precision := 2^15*p
  let band := PhaseCellBand.width p u
  let X := fun _ : ℕ => columnWords precision s t u band L q (j+2)
  let Z := fun _ : ℕ => reversedColumnWords precision s t u band L q (j+2)
  let gen := batchGeneratorPage A B precision s t u band L q (j+2)
  let outs := cstream A w (outputWeightWords q (executedOutputTable s t p u B L lo))
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
  let factors := cstream A w (reciprocalWeightWords q ((List.range B).flatMap (cellWeightRows s t p u L lo)))
  let tailX := csyms A w (reciprocalWord precision s t u band L q (j+2)) ++ (outs ++ (rhs ++ (factors ++ borrowed)))
  let S := inputSourceBank q l w B L 0 X Z [] [] tail tailX inp out
  let result := cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C)) ++ tail
  let T : Stacks 117 A := { S with R := Function.update S.R 93 result }
  have hw : w = 2*q+8 := by dsimp [q, w, executionWidth, executionPrecision]; omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, hvalid⟩ := generatedBatch_sized_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC v tail borrowed inp out
  have hregs : S.R = batchRuntimeRegisters q l B L (gen ++ (outs ++ (rhs ++ (factors ++ borrowed)))) tail := by
    funext k
    have he := inputSourceBank_R (A := A) q l B L X Z tail tailX inp out k
    simpa only [S, hw, gen, batchGeneratorPage_eq_rowBank, tailX, X, Z, List.append_assoc] using he
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseBatchRuntime_exec (body := body) B L q l
    gen outs rhs factors borrowed result v₁ T (fun _ => rfl)
    (by intro k; change Function.update S.R 93 result k = _; rw [hregs, batchRuntimeRegisters_update_result])
    (by simp [gen]; ring)
    (by simp [outs, hw, outputWeightWords, executedOutputTable])
    (by simp [rhs, hw, List.length_flatMap, Nat.mul_assoc])
    (by simp [factors, hw, reciprocalWeightWords, List.length_flatMap, Nat.mul_assoc])
  refine ⟨v₂, m₁+m₂, hu₂.trans hu₁, ?_, Exec.seq he₁ he₂, hvalid⟩
  dsimp only [sizedClosedBatchCost, q, w, j, cExp, precision, band] at hm₁ hm₂ ⊢
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
