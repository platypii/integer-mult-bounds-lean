module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedGeneratedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedClosedBatchExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBatchRuntime

/-! A fully cleaned sized batch execution, with the entire setup, arithmetic,
publication and release time ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.Main

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

noncomputable def cachedClosedWorkspace (hQ : SS.states ≤ Q) (R K p l B L s t u target rhsExp : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  cachedSetupWorkspace (P₀ := P₀) (A := A) (U := U) hQ (2^15*p) (j+1) q s t u
      (PhaseCellBand.width p u) l L B + stagedCellWorkspace R K q cExp (8*p+1) l w B L +
    mnProgPush (releaseBatchRuntime (P₀ := Empty) (Q := Q) (A := A) (U := U)) *
      releaseBatchRuntimeCost B L q l

theorem cachedClosedBatch_sized_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
    (embStk weightCacheCoreReg S₀ = cachedCoreInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B
      (fun n => (lo n).val) rhs borrowed tail inp out) →
    S₀.R 117 = batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)++cacheTail →
    (S₀.R 118).length = 2*(B*(L*w)) → S₀.R 119 = [] → S₀.R 120 = [] →
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedClosedBatchCost p l B L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S₀) + depth +
        cachedClosedWorkspace (P₀ := P₀) (A := A) (U := U) hQ R K p l B L s t u target rhsExp)
        depth (cachedClosedBatch hR hQ) (mk v S₀) m (mk v' S') ∧
      embStk weightCacheCoreReg S' = releasedCellBank rhs borrowed
        (cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C))++tail) inp out ∧
      (∀ i, 117 ≤ i.val → S'.L i = S₀.L i ∧ S'.R i = S₀.R i) := by
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
  obtain ⟨v₁,M,m₁,hu₁,hm₁,he₁,hproj,hoff₁⟩ := cachedGeneratedBatch_sized_exec_within (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hpad lo C hC v S₀ tail borrowed cacheTail inp out R K hpushR hpushK depth hinput hcache hcacheCount h119 h120
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
  have ht₂ := mn_native_exec_within he₂ _ (WordCmd.empty_native _) depth
    (mnSize (mk (embDn weightCacheCoreReg v₁) T) + depth +
      mnProgPush (releaseBatchRuntime (P₀ := Empty) (Q := Q) (A := A) (U := U)) *
        releaseBatchRuntimeCost B L q l)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm₂) _)
  have hprojT : embStk weightCacheCoreReg M = T := by
    simpa only [T,S,tailX,X,Z,result,outs,rhs,factors,precision,band,q,w,j,cExp,List.append_assoc] using hproj
  rw [← hprojT] at ht₂
  obtain ⟨v₃,F,hv₃,hu₃,he₂',hproj₃,hoff₃⟩ := exec_emb_within_stock (body' := body) (ι := Empty.elim)
    weightCacheCoreReg weightCacheCoreReg_injective (fun p => nomatch p) ht₂ v₁ rfl M rfl
  rw [hprojT] at hproj₃
  refine ⟨v₃,F,m₁+m₂,hu₃.trans (hu₂.trans hu₁),?_,mn_seq_within_add he₁ he₂',hproj₃,?_⟩
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
