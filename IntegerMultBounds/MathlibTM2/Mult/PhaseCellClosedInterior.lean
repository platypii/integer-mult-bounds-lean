module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizationHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightPrepare

/-! # Interior arithmetic with paid readiness-counter release

The retained raw inputs and scalar remain borrowed setup. All three multiplier
counters are released before the following stage generates its own readiness.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def closedInputInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq (inputInteriorFromPrecision hR hQ) ScalarPlacement.releaseWeightCounters

theorem closedInputInterior_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L cExp e j : ℕ} (hquarter : q = 4 * (cExp + e + 1)) (hw : q + (cExp + e + 1) + 4 ≤ w)
    (hq : cExp + e + 1 + j + 1 ≤ q) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z C : ℕ → List GaussianInt) (D : ℕ → List ℚ)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenC : ∀ n < M, (C n).length = L) (hlenD : ∀ n < M, (D n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hC : ∀ n < M, ∀ z ∈ C n, ‖value q z‖ ≤ (2 : ℝ) ^ cExp)
    (hD : ∀ n < M, ∀ a ∈ D n, 1 / (2 : ℝ) ^ e ≤ (a : ℝ))
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
    let tailX := csyms A w a ++ borrowed
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V) tail tailX [] inp out
    let SF := { S with R := (Function.update S.R 93
      (cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ (22 * (cExp + e + 1) + 10) + inputStageCost q cExp e w M L + interiorProductsCost q l w M L + ScalarPlacement.releaseWeightCountersCost q w ∧
      Exec body (closedInputInterior hR hQ)
        (mk v (inputSourceBank q l w M L 0 X Z ((List.range M).flatMap C)
          (reciprocalWeightWords q ((List.range M).flatMap D)) tail tailX inp out)) m (mk v' SF) ∧
      ∀ i : Fin (M * L),
        ‖value q (decodeWord (((SF.R 93).drop (i.val * w)).take w)) -
          (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
            2 / (2 : ℝ) ^ q := by
  dsimp only
  let V := fun n => weightedInputNumerators q cExp e (C n) (D n)
  let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
    tail (csyms A w a ++ borrowed) [] inp out
  let result := cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, herr⟩ := inputInteriorFromPrecision_exec (body := body)
    hR hQ hA hquarter hw hq hpad X Z C D hlenX hlenZ hlenC hlenD hX hZ hC hD a ha har
    v tail borrowed inp out
  obtain ⟨v₂, hu₂, he₂⟩ := ScalarPlacement.releaseWeightCounters_exec (body := body)
    q w v₁ S result (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      all_goals simp [S, Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start,
        Fixed.inputBank, ScalarPlacement.cr, OutputPlacement.code])
  refine ⟨v₂, m₁ + ScalarPlacement.releaseWeightCountersCost q w, hu₂.trans hu₁,
    by omega, Exec.seq he₁ he₂, ?_⟩
  intro i
  simpa only [Function.update_self] using herr i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
