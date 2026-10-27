module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGeneratedBatchExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBatchRuntime

/-! A fully cleaned sized batch execution, with the entire setup, arithmetic,
publication and release time ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

noncomputable def cachedClosedBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 121 Q A U :=
  .seq (cachedGeneratedBatch hR hQ)
    (embProg weightCacheCoreReg Empty.elim (releaseBatchRuntime (P₀ := Empty)))

def cachedClosedBatchCost (p l B L s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  cachedGeneratedBatchSetupCost (2^15*p) (j+1) q s t u (PhaseCellBand.width p u) l L B+
    stagePayloadCost B L w+cellArithmeticCost q (inputExponent p cExp) cExp (8*p+1) l w B L+
    publishFromDimensionsCost B L w+releaseBatchRuntimeCost B L q l

theorem cachedClosedBatch_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 121 Q A U) (S₀ : Stacks 121 A) (tail borrowed cacheTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
    (embStk weightCacheCoreReg S₀ = cachedCoreInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B
      (fun n => (lo n).val) rhs borrowed tail inp out) →
    S₀.R 117 = batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)++cacheTail →
    (S₀.R 118).length = 2*(B*(L*w)) → S₀.R 119 = [] → S₀.R 120 = [] →
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedClosedBatchCost p l B L s t u target rhsExp ∧
      Exec body (cachedClosedBatch hR hQ)
        (mk v S₀) m (mk v' S') ∧
      embStk weightCacheCoreReg S' = releasedCellBank rhs borrowed
        (cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C))++tail) inp out ∧
      (∀ i, 117 ≤ i.val → S'.L i = S₀.L i ∧ S'.R i = S₀.R i) ∧
      ∀ n : Fin B, (executedRun s t p u q l w B L j cExp lo C n tail).Valid s t p u (lo n) L
        (fun k => (value q (C n k)).re) (1/(2 : ℝ)^j) ((2 : ℝ)^inputExponent p cExp) := by
  dsimp only
  intro hinput hcache hcacheCount h119 h120
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
  obtain ⟨v₁,M,m₁,hu₁,hm₁,he₁,hproj,hoff₁,hvalid⟩ := cachedGeneratedBatch_sized_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC v S₀ tail borrowed cacheTail inp out hinput hcache hcacheCount h119 h120
  have hregs : S.R = batchRuntimeRegisters q l B L (gen ++ (outs ++ (rhs ++ (factors ++ borrowed)))) tail := by
    funext k
    have he := inputSourceBank_R (A := A) q l B L X Z tail tailX inp out k
    simpa only [S, hw, gen, batchGeneratorPage_eq_rowBank, tailX, X, Z, List.append_assoc] using he
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := releaseBatchRuntime_exec (body := fun p : Empty => nomatch p) B L q l
    gen outs rhs factors borrowed result (embDn weightCacheCoreReg v₁) T (fun _ => rfl)
    (by intro k; change Function.update S.R 93 result k = _; rw [hregs, batchRuntimeRegisters_update_result])
    (by simp [gen]; ring)
    (by simp [outs, hw, outputWeightWords, executedOutputTable])
    (by simp [rhs, hw, List.length_flatMap, Nat.mul_assoc])
    (by simp [factors, hw, reciprocalWeightWords, List.length_flatMap, Nat.mul_assoc])
  have hprojT : embStk weightCacheCoreReg M = T := by
    simpa only [T,S,tailX,X,Z,result,outs,rhs,factors,precision,band,q,w,j,cExp,List.append_assoc] using hproj
  rw [← hprojT] at he₂
  obtain ⟨v₃,F,he₂',hv₃,hu₃,hproj₃,hoff₃⟩ := exec_emb (body' := body) (ι := Empty.elim)
    weightCacheCoreReg_injective (fun p => nomatch p) he₂ v₁ rfl M rfl
  rw [hprojT] at hproj₃
  refine ⟨v₃,F,m₁+m₂,hu₃.trans (hu₂.trans hu₁),?_,Exec.seq he₁ he₂',hproj₃,?_,hvalid⟩
  · dsimp only [cachedClosedBatchCost,q,w,j,cExp,precision,band] at hm₁ hm₂ ⊢
    omega
  · intro i hi
    have h := hoff₃ i (by
      intro j he
      have hv := congrArg (fun k : Fin 121 => k.val) he
      dsimp [weightCacheCoreReg] at hv
      omega)
    exact ⟨h.1.trans (hoff₁ i hi).1,h.2.trans (hoff₁ i hi).2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
