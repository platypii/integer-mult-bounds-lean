module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedSetupStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchWeightRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedStagedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGeneratedBatchExec

/-! Execute raw RHS batches with retained weights through grouped arithmetic and valid publication. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.Main

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

theorem cachedGeneratedBatch_sized_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (v : HS 121 Q A U) (S₀ : Stacks 121 A) (tail borrowed cacheTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock ScalarPlacement.cr
      (rmulOne (P := Empty) (Q := Q) (A := A) (U := U) ScalarPlacement.mul
        ScalarPlacement.mul_injective (by decide) hQ ScalarPlacement.cr)) ≤ K) (depth : ℕ) :
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
    (embStk weightCacheCoreReg S₀ = cachedCoreInputBank precision (j+1) q l s t u band L B
      (fun n => (lo n).val) (cstream A w source) borrowed tail inp out) →
    S₀.R 117 = batchWeightPage A w q precision s t u B L (fun n => (lo n).val)++cacheTail →
    (S₀.R 118).length = 2*(B*(L*w)) → S₀.R 119 = [] → S₀.R 120 = [] →
    ∃ v' S' m, v'.user = v.user ∧
      m ≤ cachedGeneratedBatchSetupCost precision (j+1) q s t u band l L B +
        stagePayloadCost B L w + cellArithmeticCost q (inputExponent p cExp) cExp (8*p+1) l w B L +
        publishFromDimensionsCost B L w ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S₀) + depth +
        (cachedSetupWorkspace (P₀ := P₀) (A := A) (U := U) hQ precision (j+1) q s t u band l L B +
          stagedCellWorkspace R K q cExp (8*p+1) l w B L))
        depth (cachedGeneratedBatch hR hQ) (mk v S₀) m (mk v' S') ∧
      embStk weightCacheCoreReg S' = {S with R := (Function.update S.R 93
        (cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C))++tail))} ∧
      (∀ i, 117 ≤ i.val → S'.L i = S₀.L i ∧ S'.R i = S₀.R i) := by
  dsimp only
  intro hinput hcache hcacheCount h119 h120
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
  obtain ⟨v₁,M,m₁,hu₁,hm₁,he₁,hproj,hoff₁⟩ := cachedBatchInputBank_setup_exec_within (body := body) hQ hA
    precision (j+1) q l s t u band L B (fun n => (lo n).val) hprecision hqMax
    (Nat.pos_of_ne_zero (NeZero.ne s)) hst hu hL (cstream A w source) borrowed tail cacheTail inp out
    v S₀ (by simp [source,List.length_flatMap,hw,Nat.mul_assoc])
    hinput (by
      change S₀.R 117 = batchWeightPage A w q precision s t u B L (fun n => (lo n).val)++cacheTail at hcache
      simpa only [hw] using hcache) (by
      change (S₀.R 118).length = 2*(B*(L*w)) at hcacheCount
      simpa only [hw] using hcacheCount) h119 h120 depth
  rw [generatedBatchBank_eq_inputSourceBank] at hproj
  have houts := outputWeightRows_eq_execution_table A (2*q+8) q s t p u B L lo
  have hfs := inputWeightRows_eq_execution_table A (2*q+8) q s t p u B L lo
  dsimp only [precision] at hproj
  rw [houts,hfs,← hw] at hproj
  simp only [List.append_assoc] at hproj
  obtain ⟨v₂,T,m₂,hu₂,hm₂,he₂,hproj₂,hoff₂⟩ := cachedStagedCell_sized_exec_within
    (body := body) hR hQ hA hp hst.le hu hαu hθ hgap hbudget hL hpad lo C hC
    v₁ M tail borrowed inp out R K hpushR hpushK depth hproj
  refine ⟨v₂,T,m₁+m₂,hu₂.trans hu₁,?_,mn_seq_within_add he₁ he₂,hproj₂,?_⟩
  · dsimp only [q,w,j,cExp,precision,band] at hm₁ hm₂ ⊢
    omega
  · intro i hi
    exact ⟨(hoff₂ i hi).1.trans (hoff₁ i hi).1,(hoff₂ i hi).2.trans (hoff₁ i hi).2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
