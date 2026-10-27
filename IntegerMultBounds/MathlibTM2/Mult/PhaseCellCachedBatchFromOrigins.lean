module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedEncodedStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedBounds

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedClosedBatchSpec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardBatchOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCoreRead

/-! Use the ordinary gathered batch ABI with a retained weight key. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

noncomputable def cachedBatchFromOrigins (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P₀ 121 Q A U :=
  .seq (embProg weightCacheCoreReg Empty.elim (discardBatchOrigins (P₀ := Empty))) (cachedClosedBatch hR hQ)

def cachedBatchFromOriginsCost (p l B L s t u target rhsExp : ℕ) : ℕ :=
  discardBatchOriginsCost (2^15*p) (executionPrecision p l target rhsExp) t u B+
    cachedClosedBatchCost p l B L s t u target rhsExp

theorem cachedBatchFromOrigins_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ n < B, ∀ k, ‖value (executionPrecision p l target rhsExp) (C n k)‖ ≤ (2 : ℝ)^rhsExp)
    (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ)
    (hx : ∀ n < B, SchurDominance.Solves (realMatrix s t p u) I (x n)
      (fun k => (value (executionPrecision p l target rhsExp) (C n k)).re))
    (hfit : ∀ n < B, (lo n).val+L ≤ s)
    (hint : ∀ n < B, ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo n+(k : ZMod s)) ∧
      lo n+(k : ZMod s) ∈ I)
    (hcell : ∀ n < B, ∀ k < L, cell s t (lo n+(k : ZMod s)) = cell s t (lo n))
    (hmax : ∀ n < B, ∀ k ∈ I, cell s t k = cell s t (lo n) → ∃ i < L, lo n+(i : ZMod s) = k)
    (v : HS 121 Q A U) (S₀ : Stacks 121 A) (tail borrowed cacheTail : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
    (embStk weightCacheCoreReg S₀ = batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B
      (fun n => (lo n).val) rhs borrowed tail inp out) →
    S₀.R 117 = batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)++cacheTail →
    (S₀.R 118).length = 2*(B*(L*w)) → S₀.R 119 = [] → S₀.R 120 = [] →
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedBatchFromOriginsCost p l B L s t u target rhsExp ∧
      Exec body (cachedBatchFromOrigins hR hQ)
        (mk v S₀) m (mk v' S') ∧
      (∀ i, 117 ≤ i.val → S'.L i = S₀.L i ∧ S'.R i = S₀.R i) ∧
      (embStk weightCacheCoreReg S').inp = inp ∧ (embStk weightCacheCoreReg S').out = out ∧ (∀ k, (embStk weightCacheCoreReg S').L k = []) ∧ (embStk weightCacheCoreReg S').R 110 = rhs ++ borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg S').R k = []) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord ((((embStk weightCacheCoreReg S').R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) ((embStk weightCacheCoreReg S').R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp), ys.val.length = B*L*w ∧ (embStk weightCacheCoreReg S').R 93 = ys ++ tail := by
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
    (by rw [hinput]; simp [batchInputBank,q]) (by rw [hinput]; simp [batchInputBank,q])
    (by rw [hinput]; simp [batchInputBank,q]) (by rw [hinput]; simp [batchInputBank,q])
    (by rw [hinput]; simp [batchInputBank,q]) (by rw [hinput]; rfl) (by
      intro i hi
      rw [hinput]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals rfl)
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    weightCacheCoreReg_injective (fun p => nomatch p) hei v rfl S₀ rfl
  let T : Stacks 121 A := {S₀ with R := Function.update S₀.R 109 control}
  have he₁' : Exec body (embProg weightCacheCoreReg Empty.elim (discardBatchOrigins (P₀ := Empty)))
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
  obtain ⟨v₂,M,m₂,hu₂,hm₂,he₂,hoff,hrest⟩ := cachedClosedBatch_spec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC I x hx hfit hint hcell hmax
    v₁ T tail borrowed cacheTail inp out hinputT
    (by simpa [T] using hcache) (by simpa [T] using hcacheCount)
    (by simpa [T] using h119) (by simpa [T] using h120)
  refine ⟨v₂,M,m₁+m₂,hu₂.trans (hu₁.trans hui),?_,Exec.seq he₁' he₂,?_,hrest⟩
  · dsimp only [cachedBatchFromOriginsCost,q] at hm₁ ⊢
    omega
  · intro i hi
    have hne : i ≠ (109 : Fin 121) := by intro he; subst i; norm_num at hi
    simpa [T,hne] using hoff i hi

/-- The ordinary-origin ABI retains the cached coordinate charge, adding only a linear packet charge per cell. -/
theorem cachedBatchFromOriginsCost_eq (p l B L s t u target rhsExp : ℕ) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let V := weightWorkspaceWidth (2^15*p) q w t u
    cachedBatchFromOriginsCost p l B L s t u target rhsExp =
      cachedBatchFromOriginsCost p l 0 L s t u target rhsExp+
        (B*L)*cachedBatchCoordinateCost p l target rhsExp+
        B*(cachedBatchCellCost p l target rhsExp+12*V+9) := by
  have hw : executionWidth p l target rhsExp = 2*executionPrecision p l target rhsExp+8 := by
    unfold executionWidth executionPrecision
    omega
  dsimp only [cachedBatchFromOriginsCost]
  rw [discardBatchOriginsCost_affine (2^15*p) (executionPrecision p l target rhsExp) t u B,
    cachedClosedBatchCost_eq p l B L s t u target rhsExp,hw]
  ring

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
