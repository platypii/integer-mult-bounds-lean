module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFetchCanonical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarCanonical
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarRange

/-! # Four triangular products, merge and shared scalar in one executed chain

Generator and input numerators are ordinary raw words. The stored real scalar
is retained beneath the generator bank, fetched with generated counts, applied
and released from staging. Constructing these numerical data from the phase-cell
parameters remains a separate setup obligation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def interiorProducts (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq (mergedBranches hR)
    (.seq fetchScalar (.seq (ScalarPlacement.applyScalar hQ) (uclear 96)))

def interiorProductsCost (q l w M L : ℕ) : ℕ :=
  (6 * (M * L * w) + 6 + compactPairCost q l w (M + M) L + fixedMergeCost w M L) +
    fetchScalarCost (M + M) L w + ScalarPlacement.prepareCost q w + ScalarPlacement.runCost M L w +
    (2 * w + 2)

/-- The entire interior arithmetic chain executes without prepared execution,
readiness, skip-count or output-fit oracles. Multiplier counters and the original
retained scalar remain explicit setup data on return. -/
theorem interiorProducts_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q l w M L : ℕ} (hq : 1 ≤ q) (hw : q + 4 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X Z V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenZ : ∀ n < M, (Z n).length = L)
    (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hZ : ∀ n < M, ∀ z ∈ Z n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (a : GaussianInt) (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (tail borrowed : List (Fin (A + 4))) (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    let S := Fixed.startWithTails q l w (M + M) L L (rowBank M X Z) (rowBank M V V)
      tail (csyms A w a ++ borrowed) [] inp out
    let SF := { S with R := (Function.update (ScalarPlacement.counterR q w S.R) 93
      (cstream A w ((branchDifference q l M L X Z V).map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ interiorProductsCost q l w M L ∧
      Exec body (interiorProducts hR hQ)
        (mk v (singleBranchInputWithXTail q l w M L X Z V tail (csyms A w a ++ borrowed) inp out)) m
        (mk v' SF) ∧
      ∀ i : Fin (M * L),
        ‖value q (decodeWord (((SF.R 93).drop (i.val * w)).take w)) -
          (value q (pairNumerator q l M L X V i) - value q (pairNumerator q l M L Z V i)) * value q a‖ ≤
          2 / (2 : ℝ) ^ q := by
  dsimp only
  let ds := branchDifference q l M L X Z V
  let scalarTail := csyms A w a ++ borrowed
  let XB := rowBank M X Z
  let VB := rowBank M V V
  let S₀ := Fixed.startWithTails q l w (M + M) L L XB VB tail scalarTail [] inp out
  let SP := ScalarPlacement.scalarInputWithXTail q l w M L XB VB ds a tail scalarTail inp out
  let SD : Stacks 117 A := { SP with R := (Function.update (ScalarPlacement.counterR q w SP.R) 93
    (cstream A w (ds.map (fun x => tdivN q (x * a))) ++ tail)) }
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := mergedBranches_with_x_tail_exec (body := body) (q := q) (l := l) (w := w) (M := M) (L := L)
    hR hA hq (by omega) hpad X Z V hlenX hlenZ hlenV hX hZ hV v tail scalarTail inp out
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := fetchCanonical_exec (body := body)
    q l w (M + M) L XB VB (rowBank_length X Z hlenX hlenZ) a v₁ (cstream A w ds ++ tail) borrowed inp out
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃, _⟩ := ScalarPlacement.applyCanonical_with_x_tail_exec (body := body) (q := q) (l := l) (w := w) (M := M) (L := L)
    hQ hA hq hw XB VB ds a (by simp [ds, branchDifference])
    (branchDifference_norm hpad X Z V hlenX hlenZ hlenV hX hZ hV) ha har v₂ tail scalarTail inp out
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body 96 v₃ SD
  have hscalar : (SD.R 96).length = w := by
    simp [SD, SP, ScalarPlacement.scalarInputWithXTail, ScalarPlacement.counterR,
      ScalarPlacement.cr, OutputPlacement.code, csyms]
  refine ⟨v₄, m₁ + (m₂ + (m₃ + (2 * w + 2))), hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_, ?_⟩
  · unfold interiorProductsCost
    omega
  · refine (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [hscalar]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases h96 : k = (96 : Fin 117)
    · subst k
      simp [SD, S₀, ScalarPlacement.counterR, ScalarPlacement.cr, OutputPlacement.code,
        Fixed.startWithTails, Fixed.inputBankWithTails, Fixed.start, Fixed.inputBank]
    · by_cases h93 : k = (93 : Fin 117)
      · subst k
        simp [SD, ds]
      · have hn : k.val ≠ 93 := fun h => h93 (Fin.ext h)
        simp [SD, SP, S₀, XB, VB, scalarTail, ScalarPlacement.scalarInputWithXTail, ScalarPlacement.counterR,
          ScalarPlacement.cr, OutputPlacement.code, Fixed.startWithTails, Fixed.inputBankWithTails,
          Fixed.start, Fixed.inputBank, Function.update_apply, h96, h93, hn]
  · intro i
    simpa only [Function.update_self] using
      branchScalar_output_error (by omega) hw hpad X Z V hlenX hlenZ hlenV hX hZ hV a ha tail i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
