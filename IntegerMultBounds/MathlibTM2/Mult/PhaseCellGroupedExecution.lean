module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStagedExecution
public import IntegerMultBounds.NLogN.PhaseCellLengthGroups
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublishedAccuracy

/-! # Execution on computed equal-length cell groups

Batch count and origins come from the computed schedule. The ordinary staged
bank still contains generated numerical data and a packed per-call payload;
executing its setup/gathering and the outer group loop remains separate work.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem lengthGroup_sized_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {l L s t p u target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hkey : L ∈ lengthKeys s t (PhaseCellBand.width p u))
    (hpad : L + L ≤ 2 ^ l + 1) (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let M := (lengthGroup s t (PhaseCellBand.width p u) L).length
    let lo := groupOrigin s t (PhaseCellBand.width p u) L
    let rows := fun _ : ℕ => C
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    let j := executionStagePrecision p l target rhsExp
    let cExp := sourceExponent l target rhsExp
    let precision := 2 ^ 15 * p
    let band := PhaseCellBand.width p u
    let X : ℕ → List GaussianInt := fun _ => columnWords precision s t u band L q (j + 2)
    let Z : ℕ → List GaussianInt := fun _ => reversedColumnWords precision s t u band L q (j + 2)
    let a := reciprocalWord precision s t u band L q (j + 2)
    let source := (List.range M).flatMap (cellSourceRows L lo rows)
    let factors := reciprocalWeightWords q ((List.range M).flatMap (cellWeightRows s t p u L lo))
    let payload := cstream A w source ++ (cstream A w factors ++ borrowed)
    let tailX := csyms A w a ++ (cstream A w (outputWeightWords q (executedOutputTable s t p u M L lo)) ++ payload)
    let S := inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (publishedWords M L (executedOutputWords s t p u q l M L j cExp lo rows)) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧
      m ≤ stagePayloadCost M L w + cellArithmeticCost q (inputExponent p cExp) cExp (8 * p + 1) l w M L + publishFromDimensionsCost M L w ∧
      Exec body (stagedCell hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z [] [] tail tailX inp out))
        m (mk v' SF) ∧
      ∀ n : Fin M, (executedRun s t p u q l w M L j cExp lo rows n tail).Valid s t p u (lo n) L
        (fun k => (value q (rows n k)).re) (1 / (2 : ℝ) ^ j) ((2 : ℝ) ^ inputExponent p cExp) := by
  dsimp only
  exact stagedCell_sized_exec (body := body) hR hQ hA hp hst.le hu hαu hθ hgap hbudget
    (lengthKey_pos hst (PhaseCellBand.width p u) L hkey) hpad
    (groupOrigin s t (PhaseCellBand.width p u) L) (fun _ => C) (fun _ _ k => hC k) v tail borrowed inp out

/-- Every published row of the generated batch has the requested accuracy
against the same ambient principal interior system. -/
theorem lengthGroup_accuracy {A L s t p u l target rhsExp : ℕ} [NeZero s] {α d : ℝ}
    (hA : 4 ≤ A) (hp : 0 < p) (hst : s < t) (hu : 1 ≤ u) (hαu : α ^ 2 = (u : ℝ))
    (hθ : 0 < (t : ℝ) / s - 1) (hgap : (1 : ℝ) / 4 ≤ d * ((t : ℝ) / s - 1)) (hbudget : α ^ 2 * d ≤ p)
    (hpad : L + L ≤ 2 ^ l + 1) (C : ZMod s → GaussianInt)
    (hC : ∀ k, ‖value (executionPrecision p l target rhsExp) (C k)‖ ≤ (2 : ℝ) ^ rhsExp)
    (x : ZMod s → ℝ)
    (hx : SchurDominance.Solves (PhaseCellMatrix.realMatrix s t p u)
      (interiorSet s t (PhaseCellBand.width p u)) x
      (fun k => (value (executionPrecision p l target rhsExp) (C k)).re))
    (n : Fin (lengthGroup s t (PhaseCellBand.width p u) L).length) (i : Fin L)
    (tail : List (Fin (A + 4))) :
    let M := (lengthGroup s t (PhaseCellBand.width p u) L).length
    let lo := groupOrigin s t (PhaseCellBand.width p u) L
    let q := executionPrecision p l target rhsExp
    let w := executionWidth p l target rhsExp
    |(value q (decodeWord (((cstream A w
      (publishedWords M L (executedOutputWords s t p u q l M L (executionStagePrecision p l target rhsExp)
        (sourceExponent l target rhsExp) lo (fun _ => C))) ++ tail).drop
          ((n.val * L + i.val) * w)).take w))).re - x (lo n + (i.val : ZMod s))| ≤ 1 / (2 : ℝ) ^ target := by
  obtain ⟨hL, hfit, hint, hcell, hmax⟩ := lengthGroup_solver_geometry hst (PhaseCellBand.width p u) L n
  exact publishedCell_accuracy hA hp hst hu hαu hθ hgap hbudget hL hpad
    (groupOrigin s t (PhaseCellBand.width p u) L) (fun _ => C) (fun _ _ k => hC k) n
    (interiorSet s t (PhaseCellBand.width p u)) x hx hfit hint hcell hmax i tail

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
