module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarRun

/-! # Scalar setup and application without a prepared-readiness hypothesis -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def applyScalar (hQ : SS.states ≤ Q) : Pr P 117 Q A U := .seq prepare (run hQ)

/-- All readiness and routing counters are generated from the retained unary
headers. The actual scalar words are multiplied, decoded without aliasing, and
published while the setup counters remain explicitly installed for reuse. -/
theorem applyScalar_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q w M L : ℕ} (hq : 1 ≤ q) (hw : q + 4 ≤ w) (xs : List GaussianInt) (a : GaussianInt)
    (hlen : xs.length = M * L) (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 2)
    (ha : ‖value q a‖ ≤ 2) (har : a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hc : CClean mul S) (hfresh : ∀ r, S.R (cr r) = [])
    (hqR : (S.R 100).length = q) (hwidth : (S.R 94).length = w)
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hsrc : S.R 93 = cstream A w xs ++ tail) (hscalar : S.R 96 = csyms A w a) :
    let SF := { S with R := (Function.update (counterR q w S.R) 93
      (cstream A w (xs.map (fun x => tdivN q (x * a))) ++ tail)) }
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCost q w + runCost M L w ∧
      Exec body (applyScalar hQ) (mk v S) m (mk v' SF) ∧
      ∀ i (hi : i < xs.length),
        ‖value q (decodeWord (((SF.R 93).drop (i * w)).take w)) -
          value q (xs[i]) * value q a‖ ≤ 2 / (2 : ℝ) ^ q := by
  dsimp only
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepare_exec (body := body) q w hq hw v S hqR hwidth
    (by
      intro k hk
      have hh := (hc ⟨k.val, by omega⟩).2
      exact hh)
    (fun r _ => hfresh r)
  let SP : Stacks 117 A := { S with R := counterR q w S.R }
  have hready : Ready (fun r => SP.R (cr r)) w q := counterR_ready q w S.R hfresh
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
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := run_exec (body := body) hQ hA hw xs a hlen hxs ha har v₁ SP tail
    hready hclean hwork
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hbatch)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hrows)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hwidth)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hsrc)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hscalar)
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂, ?_⟩
  intro i hi
  simpa only [Function.update_self] using realScalar_output_error_bounded (by omega) hw xs a hxs ha tail i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
