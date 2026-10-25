module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightClose
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightedInput

/-! # The complete normalized input-weight pass

Ordinary headers and constructed reciprocal words suffice for execution with
private-workspace restoration. Its output is a legal S1 operand with the real
cell-stage tolerance; neither readiness nor output fits are assumed.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem closedWeightedInput_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w cExp e M L j : ℕ} (hw : q + (cExp + e + 1) + 4 ≤ w)
    (hq : cExp + e + 1 + j + 1 ≤ q)
    (xs : List GaussianInt) (ds : List ℚ) (hlen : xs.length = M * L) (hdslen : ds.length = xs.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ cExp)
    (hds : ∀ d ∈ ds, 1 / (2 : ℝ) ^ e ≤ (d : ℝ))
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail borrowed : List (Fin (A + 4)))
    (hc : CClean mul S) (hfresh : ∀ r, S.R (cr r) = [])
    (hqR : (S.R 100).length = q) (hbR : (S.R 116).length = cExp + e + 1) (hwR : (S.R 94).length = w)
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (htable : S.R 96 = cstream A w (reciprocalWeightWords q ds) ++ borrowed) :
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (weightedInputNumerators q cExp e xs ds) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ closedWeightsCost q (cExp + e + 1) w M L ∧
      Exec body (closedWeights hQ) (mk v S) m (mk v' SF) ∧
      (∀ z ∈ weightedInputNumerators q cExp e xs ds, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q)) ∧
      ∀ i (hi : i < xs.length),
        |(2 : ℝ) ^ (cExp + e + 1) *
            (value q (block (weightedInputNumerators q cExp e xs ds) i)).re -
          (value q xs[i]).re * (value q (reciprocalWeightWord q ds[i])).re| ≤ 1 / (2 : ℝ) ^ j := by
  dsimp only
  obtain ⟨v', m, hu, hm, he, _⟩ := closedWeights_exec (body := body)
    (q := q) (b := cExp + e + 1) (w := w) (e := cExp) (f := e) (M := M) (L := L)
    hQ hA (by omega) hw (by omega) xs (reciprocalWeightWords q ds) hlen
    (by simp [reciprocalWeightWords, hdslen]) hxs (reciprocalWeightWords_norm ds hds)
    v S tail borrowed hc hfresh hqR hbR hwR hbatch hrows hsrc htable
  exact ⟨v', m, hu, hm, he, weightedInputNumerators_disk xs ds hxs hds,
    weightedInputNumerators_error_precision hq xs ds hdslen.symm⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
