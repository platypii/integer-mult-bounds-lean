module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedClosedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchFromOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBatchRuntime

/-! Cached numerical execution from ordinary origin packets, with complete stock accounting. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Fast.Main

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

noncomputable def cachedOriginsWorkspace (hQ : SS.states ≤ Q) (R K p l B L s t u target rhsExp : ℕ) : ℕ :=
  mnProgPush (discardBatchOrigins (P₀ := Empty) (Q := Q) (A := A) (U := U)) *
      discardBatchOriginsCost (2^15*p) (executionPrecision p l target rhsExp) t u B +
    cachedClosedWorkspace (P₀ := P₀) (A := A) (U := U) hQ R K p l B L s t u target rhsExp

theorem cachedBatchFromOrigins_exec_within (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (embStk weightCacheCoreReg S₀ = batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B
      (fun n => (lo n).val) rhs borrowed tail inp out) →
    S₀.R 117 = batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)++cacheTail →
    (S₀.R 118).length = 2*(B*(L*w)) → S₀.R 119 = [] → S₀.R 120 = [] →
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedBatchFromOriginsCost p l B L s t u target rhsExp ∧
      ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S₀) + depth +
        cachedOriginsWorkspace (P₀ := P₀) (A := A) (U := U) hQ R K p l B L s t u target rhsExp)
        depth (cachedBatchFromOrigins hR hQ) (mk v S₀) m (mk v' S') ∧
      embStk weightCacheCoreReg S' = releasedCellBank rhs borrowed
        (cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C))++tail) inp out ∧
      (∀ i, 117 ≤ i.val → S'.L i = S₀.L i ∧ S'.R i = S₀.R i) := by
  dsimp only
  intro hinput hcache hcacheCount h119 h120
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
  let control := List.replicate l (tick : Fin (A+4))
  obtain ⟨vi,m₁,hui,hm₁,hei⟩ := discardBatchOrigins_exec
    (body := fun p : Empty => nomatch p) (2^15*p) q t u B (fun n => (lo n).val)
    (embDn weightCacheCoreReg v) (embStk weightCacheCoreReg S₀) control
    (by rw [hinput]; simp [batchInputBank]) (by rw [hinput]; simp [batchInputBank,q])
    (by rw [hinput]; simp [batchInputBank]) (by rw [hinput]; simp [batchInputBank])
    (by rw [hinput]; simp [batchInputBank]) (by rw [hinput]; rfl) (by
      intro i hi
      rw [hinput]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rfl)
  have hti := mn_native_exec_within hei _ (WordCmd.empty_native _) depth
    (mnSize (mk (embDn weightCacheCoreReg v) (embStk weightCacheCoreReg S₀)) + depth +
      mnProgPush (discardBatchOrigins (P₀ := Empty) (Q := Q) (A := A) (U := U)) *
        discardBatchOriginsCost (2^15*p) q t u B)
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm₁) _)
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr_within_stock (body' := body) (ι := Empty.elim)
    weightCacheCoreReg weightCacheCoreReg_injective (fun p => nomatch p) hti v rfl S₀ rfl
  let T : Stacks 121 A := {S₀ with R := Function.update S₀.R 109 control}
  have he₁' : ExecWithin body (fun level z => mnSize z + level ≤ mnSize (mk v S₀) + depth +
      mnProgPush (discardBatchOrigins (P₀ := Empty) (Q := Q) (A := A) (U := U)) *
        discardBatchOriginsCost (2^15*p) q t u B) depth (embProg weightCacheCoreReg Empty.elim (discardBatchOrigins (P₀ := Empty)))
      (mk v S₀) m₁ (mk v₁ T) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    rw [embOvr_updR weightCacheCoreReg_injective,embOvr_stk]
    rfl
  have hview : embStk weightCacheCoreReg T =
      {embStk weightCacheCoreReg S₀ with R := Function.update (embStk weightCacheCoreReg S₀).R 109 control} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    simp [T,embStk,weightCacheCoreReg,Function.update_apply,Fin.ext_iff]
  have hinputT : embStk weightCacheCoreReg T =
      cachedCoreInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B
        (fun n => (lo n).val) rhs borrowed tail inp out := by
    rw [hview,hinput]
    rfl
  obtain ⟨v₂,M,m₂,hu₂,hm₂,he₂,hproj,hoff⟩ := cachedClosedBatch_sized_exec_within (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hpad lo C hC
    v₁ T tail borrowed cacheTail inp out R K hpushR hpushK depth hinputT
    (by simpa [T] using hcache) (by simpa [T] using hcacheCount)
    (by simpa [T] using h119) (by simpa [T] using h120)
  refine ⟨v₂,M,m₁+m₂,hu₂.trans (hu₁.trans hui),?_,mn_seq_within_add he₁' he₂,hproj,?_⟩
  · dsimp only [cachedBatchFromOriginsCost,q] at hm₁ ⊢
    omega
  · intro i hi
    have hne : i ≠ (109 : Fin 121) := by intro he; subst i; norm_num at hi
    simpa [T,hne] using hoff i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
