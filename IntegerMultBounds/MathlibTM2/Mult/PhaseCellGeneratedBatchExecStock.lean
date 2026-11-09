module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBatchExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBankStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStagedStock

/-! Sized execution starts at the original batch bank with shared setup and arithmetic reserves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem generatedBatch_trace_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {v₀ v₁ v₂ : HS 117 Q A U} {S₀ S₁ S₂ : Stacks 117 A} {m₁ m₂ work₁ work₂ depth : ℕ}
    (h₁ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+work₁) depth
      (generatedBatchSetup hQ) (mk v₀ S₀) m₁ (mk v₁ S₁))
    (h₂ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+work₂) depth
      (stagedCell hR hQ) (mk v₁ S₁) m₂ (mk v₂ S₂)) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₀ S₀)+depth+(work₁+work₂)) depth
      (generatedBatch hR hQ) (mk v₀ S₀) (m₁+m₂) (mk v₂ S₂) :=
  mn_seq_within_add h₁ h₂

theorem generatedBatch_sized_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (J R K : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := P₀) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ J)
    (hpushR : mnProgPush (rpProg (P := P₀) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr
      (rmulOne (P := P₀) (Q := Q) (A := A) (U := U) mul mul_injective (by decide) hQ cr)) ≤ K)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let precision := 2^15*p
    let band := PhaseCellBand.width p u
    let source := (List.range B).flatMap (cellSourceRows L lo C)
    let factors := reciprocalWeightWords q ((List.range B).flatMap (cellWeightRows s t p u L lo))
    let payload := cstream A w source ++ (cstream A w factors ++ borrowed)
    let tailX := csyms A w (reciprocalWord precision s t u band L q (j+2)) ++
      (cstream A w (outputWeightWords q (executedOutputTable s t p u B L lo)) ++ payload)
    let S := inputSourceBank q l w B L 0
      (fun _ => columnWords precision s t u band L q (j+2))
      (fun _ => reversedColumnWords precision s t u band L q (j+2)) [] [] tail tailX inp out
    ∃ v' m, v'.user = v.user ∧
      m ≤ generatedBatchSetupCost precision (j+1) q s t u band l L B +
        stagePayloadCost B L w + cellArithmeticCost q (inputExponent p cExp) cExp (8*p+1) l w B L +
        publishFromDimensionsCost B L w ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤
          mnSize (mk v (batchInputBank precision (j+1) q l s t u band L B (fun n => (lo n).val)
            (cstream A w source) borrowed tail inp out))+depth+
          (generatedBatchSetupWorkspace J precision (j+1) q s t u band l L B+
            stagedCellWorkspace R K q cExp (8*p+1) l w B L))
        depth (generatedBatch hR hQ)
        (mk v (batchInputBank precision (j+1) q l s t u band L B (fun n => (lo n).val)
          (cstream A w source) borrowed tail inp out)) m
        (mk v' { S with R := (Function.update S.R 93
          (cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C)) ++ tail)) })) ∧
      ∀ n : Fin B, (executedRun s t p u q l w B L j cExp lo C n tail).Valid s t p u (lo n) L
        (fun k => (value q (C n k)).re) (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let precision := 2^15*p
  let band := PhaseCellBand.width p u
  let source := (List.range B).flatMap (cellSourceRows L lo C)
  have hw : w = 2*q+8 := by dsimp [q, w, executionWidth, executionPrecision]; omega
  have hprecision : 13 ≤ precision := by dsimp [precision]; omega
  have hqMax : q ≤ 2*((j+1)+1) := by
    dsimp [q, j, executionPrecision, executionStagePrecision]
    omega
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := batchInputBank_setup_exec_within (body := body) hQ hA
    precision (j+1) q l s t u band L B (fun n => (lo n).val) hprecision hqMax
    (Nat.pos_of_ne_zero (NeZero.ne s)) hst hu hL hLs (fun i _ => ZMod.val_lt (lo i))
    (cstream A w source) borrowed tail inp out J hpushJ v (by
      simp [source, List.length_flatMap, hw, Nat.mul_assoc])
  have houts := outputWeightRows_eq_execution_table A (2*q+8) q s t p u B L lo
  have hfs := inputWeightRows_eq_execution_table A (2*q+8) q s t p u B L lo
  dsimp only [precision] at he₁
  rw [houts, hfs, ← hw] at he₁
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂, hvalid⟩ := stagedCell_sized_exec (body := body)
    hR hQ hA hp hst.le hu hαu hθ hgap hbudget hL hpad lo C hC v₁ tail borrowed inp out
  have he₁' := he₁
  simp only [List.append_assoc] at he₁'
  refine ⟨v₂, m₁+m₂, hu₂.trans hu₁, ?_, ?_, hvalid⟩
  · dsimp only [q, w, j, cExp, precision, band] at hm₁ hm₂ ⊢
    omega
  · intro depth
    obtain ⟨vf,nf,_,_,hf⟩ := stagedCell_sized_exec_within (body := body)
      hR hQ hA hp hst.le hu hαu hθ hgap hbudget hL hpad lo C hC v₁ tail borrowed inp out
      R K hpushR hpushK depth
    obtain ⟨heqn,heqF⟩ := hf.toExec.unique he₂
    rw [heqn,heqF] at hf
    exact generatedBatch_trace_within hR hQ (he₁' depth) hf

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
