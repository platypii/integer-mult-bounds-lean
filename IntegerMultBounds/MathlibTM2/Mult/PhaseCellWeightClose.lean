module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightApply

/-! # Weight application with complete private-workspace restoration

Counter generation, operand routing, normalization, output publication and
counter release are all executed. The ordinary retained headers and weight
source survive; only the persistent output prefix changes.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def closedWeights (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq (applyWeights hQ) releaseWeightCounters

def closedWeightsCost (q b w M L : ℕ) : ℕ :=
  prepareWeightsCost q b w + runWeightsCost M L w + releaseWeightCountersCost (q + b) w

/-- Ordinary unary headers and raw operand words suffice for the complete
117-tape weight pass. No readiness, routing-count or output-fit oracle remains. -/
theorem closedWeights_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q b w e f M L : ℕ} (hq : 1 ≤ q) (hwidth : q + b + 4 ≤ w) (hmag : q + (e + f) + 2 ≤ w)
    (xs factors : List GaussianInt) (hlen : xs.length = M * L) (hfactors : factors.length = xs.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ e)
    (hf : ∀ a ∈ factors, ‖value q a‖ ≤ (2 : ℝ) ^ f ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail borrowed : List (Fin (A + 4)))
    (hc : CClean mul S) (hfresh : ∀ r, S.R (cr r) = [])
    (hqR : (S.R 100).length = q) (hbR : (S.R 116).length = b) (hwR : (S.R 94).length = w)
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hsrc : S.R 93 = cstream A w xs ++ tail) (htable : S.R 96 = cstream A w factors ++ borrowed) :
    let SF := { S with R := (Function.update S.R 93
      (cstream A w (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs factors) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ closedWeightsCost q b w M L ∧
      Exec body (closedWeights hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        ‖value q (decodeWord (((SF.R 93).drop (i * w)).take w)) -
          value q xs[i] * value q factors[i] / (2 : ℂ) ^ b‖ ≤ 2 / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁, herr⟩ := applyWeights_exec (body := body)
    (q := q) (b := b) (w := w) (e := e) (f := f) (M := M) (L := L)
    hQ hA hq hwidth hmag xs factors hlen hfactors hxs hf v S tail borrowed hc hfresh
    hqR hbR hwR hbatch hrows hsrc htable
  obtain ⟨v₂, hu₂, he₂⟩ := releaseWeightCounters_exec (body := body) (q + b) w v₁ S
    (cstream A w (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs factors) ++ tail)
    (fun r _ => hfresh r)
  refine ⟨v₂, m₁ + releaseWeightCountersCost (q + b) w, hu₂.trans hu₁,
    by unfold closedWeightsCost; omega, Exec.seq he₁ he₂, ?_⟩
  intro i hi
  simpa only [Function.update_self] using herr i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
