module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedBatchFromOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaBatchOrder

/-! Run all RHS/cell pairs of one interior key in a single cached batch.
The ordinary cached ABI orders replicas first and cells second. Ambient setup
is outside the replica factor; output certificates use the same physical order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Replicas share the complete native startup, including ambient unary headers. -/
theorem replicaInteriorBatchCost_eq (p l N B L s t u target rhsExp : ℕ) :
    cachedBatchFromOriginsCost p l (N*B) L s t u target rhsExp =
      cachedBatchFromOriginsCost p l 0 L s t u target rhsExp+
      N*((B*L)*cachedBatchCoordinateCost p l target rhsExp+
        B*(cachedBatchCellCost p l target rhsExp+
          12*weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
            (executionWidth p l target rhsExp) t u+9)) := by
  rw [cachedBatchFromOriginsCost_eq]
  ring

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 121 Q A U}

/-- This is the existing fixed cached program, not one call per replica. Each
returned row is certified against its own RHS and the original ambient matrix. -/
theorem replicaInteriorBatch_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l N B L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hB : 0 < B) (hL : 0 < L) (hLs : L ≤ s) (hpad : L+L ≤ 2^l+1)
    (lo : ℕ → ZMod s) (C : ℕ → ZMod s → GaussianInt)
    (hC : ∀ r < N, ∀ k, ‖value (executionPrecision p l target rhsExp) (C r k)‖ ≤ (2 : ℝ)^rhsExp)
    (I : Finset (ZMod s)) (x : ℕ → ZMod s → ℝ)
    (hx : ∀ r < N, SchurDominance.Solves (realMatrix s t p u) I (x r)
      (fun k => (value (executionPrecision p l target rhsExp) (C r k)).re))
    (hfit : ∀ j < B, (lo j).val+L ≤ s)
    (hint : ∀ j < B, ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo j+(k : ZMod s)) ∧
      lo j+(k : ZMod s) ∈ I)
    (hcell : ∀ j < B, ∀ k < L, cell s t (lo j+(k : ZMod s)) = cell s t (lo j))
    (hmax : ∀ j < B, ∀ k ∈ I, cell s t k = cell s t (lo j) → ∃ i < L, lo j+(i : ZMod s) = k)
    (v : HS 121 Q A U) (S : Stacks 121 A) (tail borrowed cacheTail : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let origins := fun n => lo (n%B)
    let rhs := cstream A w ((List.range N).flatMap (fun r =>
      (List.range B).flatMap (cellSourceRows L lo (fun _ => C r))))
    embStk weightCacheCoreReg S = batchInputBank (2^15*p) (j+1) q l s t u
      (PhaseCellBand.width p u) L (N*B) (fun n => (origins n).val) rhs borrowed tail inp out →
    S.R 117 = batchWeightPage A w q (2^15*p) s t u (N*B) L (fun n => (origins n).val)++cacheTail →
    (S.R 118).length = 2*((N*B)*(L*w)) → S.R 119 = [] → S.R 120 = [] →
    ∃ v' F m, v'.user = v.user ∧
      m ≤ cachedBatchFromOriginsCost p l 0 L s t u target rhsExp+
        N*((B*L)*cachedBatchCoordinateCost p l target rhsExp+B*(cachedBatchCellCost p l target rhsExp+
          12*weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
            (executionWidth p l target rhsExp) t u+9)) ∧
      Exec body (cachedBatchFromOrigins hR hQ) (mk v S) m (mk v' F) ∧
      (∀ i, 117 ≤ i.val → F.L i = S.L i ∧ F.R i = S.R i) ∧
      (embStk weightCacheCoreReg F).inp = inp ∧ (embStk weightCacheCoreReg F).out = out ∧
      (∀ k, (embStk weightCacheCoreReg F).L k = []) ∧
      (embStk weightCacheCoreReg F).R 110 = rhs++borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → (embStk weightCacheCoreReg F).R k = []) ∧
      (∀ r : Fin N, ∀ j : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo j) L)
        (publishedBatchRead q w (r.val*B+j.val) L (lo j) ((embStk weightCacheCoreReg F).R 93))
        (x r) (1/(2 : ℝ)^target)) ∧
      ∃ ys : BoundedEncodedStream A w q (interiorOutputExponent p l target rhsExp),
        ys.val.length = (N*B)*L*w ∧ (embStk weightCacheCoreReg F).R 93 = ys++tail := by
  dsimp only
  intro hinput hcache hcount h119 h120
  have hr (n : ℕ) (hn : n < N*B) : n/B < N := (Nat.div_lt_iff_lt_mul hB).mpr hn
  have hj (n : ℕ) : n%B < B := Nat.mod_lt n hB
  obtain ⟨v',F,m,huser,hcost,he,hframe,hI,hO,hleft,hsource,hblank,_,herror,hys⟩ :=
    cachedBatchFromOrigins_spec (body := body) hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad
      (fun n => lo (n%B)) (fun n => C (n/B)) (fun n hn => hC _ (hr n hn)) I
      (fun n => x (n/B)) (fun n hn => hx _ (hr n hn))
      (fun n _ => hfit _ (hj n)) (fun n _ => hint _ (hj n))
      (fun n _ => hcell _ (hj n)) (fun n _ => hmax _ (hj n))
      v S tail borrowed cacheTail inp out
      (by simpa only [replicaInteriorRows_eq N B L hB lo C] using hinput) hcache hcount h119 h120
  rw [replicaInteriorBatchCost_eq] at hcost
  refine ⟨v',F,m,huser,hcost,he,hframe,hI,hO,hleft,?_,hblank,?_,hys⟩
  · simpa only [replicaInteriorRows_eq N B L hB lo C] using hsource
  intro r j
  have hindex : r.val*B+j.val < N*B := by nlinarith only [r.isLt,j.isLt]
  have hi := replicaCell_index hB r.val j.val j.isLt
  have he := herror ⟨r.val*B+j.val,hindex⟩
  simpa only [hi.1,hi.2] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
