module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCellExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedAccuracy
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreRead

/-! A paid, fully cleaned single-cell endpoint with requested accuracy for the
actual output tape. Geometry stays in the original ambient coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem closedCell_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hL : 0 < L) (hpad : L + L ≤ 2 ^ l + 1) (lo : ZMod s) (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (I : Finset (ZMod s)) (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (realMatrix s t p u) I x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (hfit : lo.val + L ≤ s)
    (hint : ∀ k < L, Interior s t (PhaseCellBand.width p u) (lo + (k : ZMod s)) ∧ lo + (k : ZMod s) ∈ I)
    (hcell : ∀ k < L, cell s t (lo + (k : ZMod s)) = cell s t lo)
    (hmax : ∀ k ∈ I, cell s t k = cell s t lo → ∃ i < L, lo + (i : ZMod s) = k)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let rhs := cstream A w ((List.range 1).flatMap (cellSourceRows L (fun _ => lo) (fun _ => C)))
    ∃ v' S' m, v'.user = v.user ∧ m ≤ sizedClosedCellCost p l L s t u target rhsExp lo.val ∧
      Exec body (closedCell hR hQ)
        (mk v (unaryCellBank (2 ^ 15 * p) (j + 1) q l s t u (PhaseCellBand.width p u) L lo.val rhs borrowed tail inp out))
        m (mk v' S') ∧
      S'.inp = inp ∧ S'.out = out ∧ (∀ k, S'.L k = []) ∧ S'.R 110 = rhs ++ borrowed ∧
      (∀ k : Fin 117, k ≠ 93 → k ≠ 110 → S'.R k = []) ∧
      (∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop (i.val * w)).take w))).re -
        x (lo + (i.val : ZMod s))| ≤ 1 / (2 : ℝ) ^ target) ∧
      PhaseCellInterface.ErrorOn (publishedCellCore lo L) (publishedCellRead q w lo (S'.R 93)) x
        (1 / (2 : ℝ) ^ target) := by
  dsimp only
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  let j := executionStagePrecision p l target rhsExp
  let cExp := sourceExponent l target rhsExp
  let rhs := cstream A w ((List.range 1).flatMap (cellSourceRows L (fun _ => lo) (fun _ => C)))
  let result := cstream A w (publishedWords 1 L
    (executedOutputWords s t p u q l 1 L j cExp (fun _ => lo) (fun _ => C))) ++ tail
  let S' := releasedCellBank rhs borrowed result inp out
  obtain ⟨v', m, huser, hm, he, _⟩ := closedCell_sized_exec (body := body) hR hQ hA hp hst hu
    hαu hθ hgap hbudget hL (by omega) hpad lo C hC v tail borrowed inp out
  have hpoint : ∀ i : Fin L, |(value q (decodeWord (((S'.R 93).drop (i.val * w)).take w))).re -
      x (lo + (i.val : ZMod s))| ≤ 1 / (2 : ℝ) ^ target := by
    intro i
    have hacc := publishedCell_accuracy (M := 1) (by omega : 4 ≤ A) hp hst hu hαu hθ hgap hbudget
      hL hpad (fun _ => lo) (fun _ => C) (fun _ _ k => hC k) (0 : Fin 1) I x hx
      hfit hint hcell hmax i tail
    simpa [S', releasedCellBank, result, q, w, j, cExp] using hacc
  refine ⟨v', S', m, huser, hm, he, rfl, rfl, fun _ => rfl, ?_, ?_, hpoint, ?_⟩
  · simp [S', releasedCellBank, rhs, w]
  · intro k hk93 hk110
    have h93 : k.val ≠ 93 := fun h => hk93 (Fin.ext h)
    have h110 : k.val ≠ 110 := fun h => hk110 (Fin.ext h)
    simp [S', releasedCellBank, h93, h110]
  · exact publishedCellRead_errorOn q w lo (S'.R 93) x _ hfit hpoint

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
