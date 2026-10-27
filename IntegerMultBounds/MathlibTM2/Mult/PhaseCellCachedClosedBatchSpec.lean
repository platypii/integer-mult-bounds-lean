module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundedEncodedStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedBounds

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedClosedBatchExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchCoreRead

/-! Fully cleaned batch execution with requested accuracy on every original
ambient core. The error is independent of the number of published cells. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 121 Q A U}

theorem cachedClosedBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (embStk weightCacheCoreReg S₀ = cachedCoreInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B
      (fun n => (lo n).val) rhs borrowed tail inp out) →
    S₀.R 117 = batchWeightPage A w q (2^15*p) s t u B L (fun n => (lo n).val)++cacheTail →
    (S₀.R 118).length = 2*(B*(L*w)) → S₀.R 119 = [] → S₀.R 120 = [] →
    ∃ v' S' m, v'.user = v.user ∧ m ≤ cachedClosedBatchCost p l B L s t u target rhsExp ∧
      Exec body (cachedClosedBatch hR hQ)
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
  let cExp := sourceExponent l target rhsExp
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
  let result := cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C)) ++ tail
  let E := releasedCellBank rhs borrowed result inp out
  obtain ⟨v',M,m,huser,hm,he,hproj,hoff,_⟩ := cachedClosedBatch_sized_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC v S₀ tail borrowed cacheTail inp out hinput hcache hcacheCount h119 h120
  have hpoint : ∀ n : Fin B, ∀ i : Fin L,
      |(value q (decodeWord (((E.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target := by
    intro n i
    have hacc := publishedCell_accuracy (by omega : 4 ≤ A) hp hst hu hαu hθ hgap hbudget
      hL hpad lo C hC n I (x n) (hx n n.isLt) (hfit n n.isLt) (hint n n.isLt)
      (hcell n n.isLt) (hmax n n.isLt) i tail
    simpa [E, releasedCellBank, result, q, w, j, cExp] using hacc
  refine ⟨v',M,m,huser,hm,he,hoff,?_⟩
  rw [hproj]
  refine ⟨rfl,rfl,fun _ => rfl,?_,?_,hpoint,?_,?_⟩
  · simp [E, releasedCellBank, rhs, w]
  · intro k hk93 hk110
    have h93 : k.val ≠ 93 := fun h => hk93 (Fin.ext h)
    have h110 : k.val ≠ 110 := fun h => hk110 (Fin.ext h)
    simp [E, releasedCellBank, h93, h110]
  · intro n
    exact publishedBatchRead_errorOn q w n.val (lo n) (E.R 93) (x n) _ (hfit n n.isLt) (hpoint n)
  · refine ⟨boundedEncodedStream A w q (interiorOutputExponent p l target rhsExp)
      (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C))
      (publishedOutputWords_norm hp hst hu hL hαu hθ hgap hbudget hpad lo C hC), ?_, rfl⟩
    simp [w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
