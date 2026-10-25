module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightRoute
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarFinish
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream

/-! # Routed aligned weight arithmetic on the shared 117-tape bank

The caller supplies multiplier readiness at the explicit shift precision. All
routing counts are generated, all staging is released and only the ordered
output prefix changes. The persistent table, including its suffix, is restored.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def runWeights (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq routeWeights (.seq (realWeightStream cr mul mul_injective (by decide) hQ) finish)

def runWeightsCost (M L w : ℕ) : ℕ :=
  routeWeightsCost M L w + (M * L) * (rmulCost w + 14 * w + 2) + 16

/-- Route, multiply aligned real weights, release operand copies and publish.
The combined normalization shift is data in the multiplier counters. -/
theorem runWeights_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {q b w e f M L : ℕ} (hw : q + (e + f) + 2 ≤ w) (hshift : q + b ≤ w)
    (xs factors : List GaussianInt) (hlen : xs.length = M * L) (hfactors : factors.length = xs.length)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ (2 : ℝ) ^ e)
    (hf : ∀ a ∈ factors, ‖value q a‖ ≤ (2 : ℝ) ^ f ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail borrowed : List (Fin (A + 4)))
    (hr : Ready (fun r => S.R (cr r)) w (q + b)) (hc : CClean mul S)
    (hwork : ∀ r ∈ [CR.xs, .ys, .xsv, .ysv, .acc, .out], S.R (cr r) = [])
    (hbatch : (S.R 108).length = M + M) (hrows : (S.R 103).length = L)
    (hwidth : (S.R 94).length = w)
    (hsrc : S.R 93 = cstream A w xs ++ tail)
    (htable : S.R 96 = cstream A w factors ++ borrowed) :
    ∃ v' m, v'.user = v.user ∧ m ≤ runWeightsCost M L w ∧
      Exec body (runWeights hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R 93
          (cstream A w (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs factors) ++ tail)) }) := by
  have hsmall (k : Fin 117) (hk : k.val < 64) : S.R k = [] := by
    have hh := (hc ⟨k.val, hk⟩).2
    exact hh
  have h84 : S.R 84 = [] := hwork .xs (by simp)
  have h85 : S.R 85 = [] := hwork .ys (by simp)
  have h89 : S.R 89 = [] := hwork .out (by simp)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := routeWeights_exec (body := body) M L w xs factors hlen hfactors v S tail borrowed
    hbatch hrows hwidth hsrc htable (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hsmall _ (by decide) | exact h84 | exact h85)
  let SR : Stacks 117 A := { S with R := routeR S.R (cstream A w xs) tail (cstream A w factors) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := realWeightStream_exec (body := body)
    (q := q) (b := b) (w := w) (e := e) (f := f)
    cr_injective cr_mul mul_injective (by decide) hQ hA hw hshift
    xs factors hfactors.symm hxs hf v₁ SR
    (routeR_clean S _ _ _ hc) (routeR_ready (q + b) w S.R _ _ _ hr)
    (by simp [SR, routeR, cr, OutputPlacement.code])
    (by simp [SR, routeR, cr, OutputPlacement.code])
    (by simpa [SR, routeR, cr, OutputPlacement.code] using hwork .xsv (by simp))
    (by simpa [SR, routeR, cr, OutputPlacement.code] using hwork .ysv (by simp))
    (by simpa [SR, routeR, cr, OutputPlacement.code] using hwork .acc (by simp))
  have ho : SR.R (cr .out) = [] := by simp [SR, routeR, cr, OutputPlacement.code, h89]
  rw [ho, List.append_nil] at he₂
  have he₂' : Exec body (realWeightStream cr mul mul_injective (by decide) hQ) (mk v₁ SR) m₂
      (mk v₂ { S with R := (Function.update (routeR S.R (cstream A w xs) tail (cstream A w factors))
        89 (cstream A w (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs factors))) }) := by
    simpa only [SR, show cr .out = (89 : Fin 117) from rfl] using he₂
  obtain ⟨v₃, hu₃, he₃⟩ := finish_stream_exec (body := body) w xs
    (List.zipWith (fun x a => tdivN (q + b) (x * a)) xs factors) factors
    (by simp [hfactors]) v₂ S tail (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact hsmall _ (by decide)
      · exact h84
      · exact h85
      · exact h89)
  refine ⟨v₃, m₁ + (m₂ + (6 * (xs.length * w) + 2 * (factors.length * w) + 8)),
    hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂' he₃)⟩
  · rw [hlen] at hm₂
    rw [hfactors, hlen]
    unfold runWeightsCost
    nlinarith only [hm₁, hm₂]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
