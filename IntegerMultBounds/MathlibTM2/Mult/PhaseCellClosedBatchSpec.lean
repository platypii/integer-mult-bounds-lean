module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBatchExec
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

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem closedBatch_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A+4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
    ∃ v' S' m, v'.user = v.user ∧ m ≤ sizedClosedBatchCost p l B L s t u target rhsExp ∧
      Exec body (closedBatch hR hQ)
        (mk v (batchInputBank (2^15*p) (j+1) q l s t u (PhaseCellBand.width p u) L B (fun n => (lo n).val)
          rhs borrowed tail inp out)) m (mk v' S') ∧
      S'.inp = inp ∧ S'.out = out ∧ (∀ k, S'.L k = []) ∧ S'.R 110 = rhs ++ borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      (∀ n : Fin B, ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target) ∧
      (∀ n : Fin B, PhaseCellInterface.ErrorOn (publishedCellCore (lo n) L)
        (publishedBatchRead q w n.val L (lo n) (S'.R 93)) (x n) (1/(2 : ℝ)^target)) ∧
      ∃ ys : List (Fin (A+4)), ys.length = B*L*w ∧ S'.R 93 = ys ++ tail := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let rhs := cstream A w ((List.range B).flatMap (cellSourceRows L lo C))
  let result := cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C)) ++ tail
  let S' := releasedCellBank rhs borrowed result inp out
  obtain ⟨v', m, huser, hm, he, _⟩ := closedBatch_sized_exec (body := body)
    hR hQ hA hp hst hu hαu hθ hgap hbudget hL hLs hpad lo C hC v tail borrowed inp out
  have hpoint : ∀ n : Fin B, ∀ i : Fin L,
      |(value q (decodeWord (((S'.R 93).drop ((n.val*L+i.val)*w)).take w))).re -
        x n (lo n+(i.val : ZMod s))| ≤ 1/(2 : ℝ)^target := by
    intro n i
    have hacc := publishedCell_accuracy (by omega : 4 ≤ A) hp hst hu hαu hθ hgap hbudget
      hL hpad lo C hC n I (x n) (hx n n.isLt) (hfit n n.isLt) (hint n n.isLt)
      (hcell n n.isLt) (hmax n n.isLt) i tail
    simpa [S', releasedCellBank, result, q, w, j, cExp] using hacc
  refine ⟨v', S', m, huser, hm, he, rfl, rfl, fun _ => rfl, ?_, ?_, hpoint, ?_, ?_⟩
  · simp [S', releasedCellBank, rhs, w]
  · intro k hk93 hk110
    have h93 : k.val ≠ 93 := fun h => hk93 (Fin.ext h)
    have h110 : k.val ≠ 110 := fun h => hk110 (Fin.ext h)
    simp [S', releasedCellBank, h93, h110]
  · intro n
    exact publishedBatchRead_errorOn q w n.val (lo n) (S'.R 93) (x n) _ (hfit n n.isLt) (hpoint n)
  · refine ⟨cstream A w (publishedWords B L (executedOutputWords s t p u q l B L j cExp lo C)), ?_, rfl⟩
    simp [w]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
