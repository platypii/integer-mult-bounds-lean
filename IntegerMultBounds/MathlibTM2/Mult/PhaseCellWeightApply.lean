module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightPrepare
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightRun

/-! # Weight application with executed readiness and routing setup

Ordinary headers carry grid precision, normalization, width and batch dimensions.
The program generates the combined-shift readiness counters and routes the
weight stream itself. No prepared-readiness or output-fit oracle is supplied.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def applyWeights (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq prepareWeights (runWeights hQ)

/-- Execute readiness generation, routing, normalization and publication. The
three counters are retained explicitly; all other private workspace is restored. -/
theorem applyWeights_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q b w e f M L : ℕ} (hq : 1 ≤ q) (hwidth : q + b + 4 ≤ w) (hmag : q + (e + f) + 2 ≤ w)
    (xs factors : List GaussianInt) (hlen : xs.length = M * L) (hfactors : factors.length = xs.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ e)
    (hf : ∀ a ∈ factors, ‖value q a‖ ≤ (2 : ℝ) ^ f ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail borrowed : List (Fin (A + 4)))
    (hc : CClean mul S) (hfresh : ∀ r, S.R (cr r) = [])
    (hqR : (S.R 100).length = q) (hbR : (S.R 116).length = b) (hwR : (S.R 94).length = w)
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hsrc : S.R 93 = cstream A w xs ++ tail) (htable : S.R 96 = cstream A w factors ++ borrowed) :
    let SF := { S with R := (Function.update (counterR (q + b) w S.R) 93
      (cstream A w (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs factors) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareWeightsCost q b w + runWeightsCost M L w ∧
      Exec body (applyWeights hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        ‖value q (decodeWord (((SF.R 93).drop (i * w)).take w)) -
          value q xs[i] * value q factors[i] / (2 : ℂ) ^ b‖ ≤ 2 / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepareWeights_exec (body := body) q b w hq hwidth v S hqR hbR hwR
    (by intro k hk; exact (hc ⟨k.val, by omega⟩).2)
    (fun r _ => hfresh r)
  let SP : Stacks 117 A := { S with R := counterR (q + b) w S.R }
  have hready : Ready (fun r => SP.R (cr r)) w (q + b) := counterR_ready (q + b) w S.R hfresh
  have hclean : CClean mul SP := by
    intro i
    constructor
    · exact (hc i).1
    · have hh := (hc i).2
      simpa [SP, counterR, (cr_mul .wn i).symm, (cr_mul .pn i).symm, (cr_mul .nn i).symm] using hh
  have hwork : ∀ r ∈ [CR.xs, .ys, .xsv, .ysv, .acc, .out], SP.R (cr r) = [] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SP, counterR, cr_injective.eq_iff, hfresh]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := runWeights_exec (body := body) hQ hA hmag (by omega)
    xs factors hlen hfactors hxs hf v₁ SP tail borrowed hready hclean hwork
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hbatch)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hrows)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hwR)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hsrc)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using htable)
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, ?_⟩
  intro i hi
  simpa only [Function.update_self] using realWeightStream_output_error (b := b) (by omega) hmag
    xs factors hfactors.symm hxs (fun a ha => (hf a ha).1) tail i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
