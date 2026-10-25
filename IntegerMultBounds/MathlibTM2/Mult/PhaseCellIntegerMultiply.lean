module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarPrepare

/-! # Exact integer product streams with executed readiness

The existing signed multiplier runs at truncation precision zero. Its counters
are generated from the retained width header, rather than supplied as readiness.
Operands and every scratch port are restored; the three counters remain for reuse.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem tdivN_precision_zero (z : GaussianInt) : tdivN 0 z = z := by
  ext <;> simp [tdivN]

namespace ScalarPlacement

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def integerProducts (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq prepare (realWeightStream cr mul mul_injective (by decide) hQ)

/-- The actual zero-precision stream computes exact integer products modulo the
word width. An output-fit proof is needed only for signed decoding. -/
theorem integerProducts_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w : ℕ} (hw : 5 ≤ w) (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hc : CClean mul S)
    (hwork : ∀ r, r ∉ [CR.xs, .ys, .out] → S.R (cr r) = [])
    (hqR : (S.R 100).length = 0) (hwR : (S.R 94).length = w)
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w as) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ prepareCost 0 w + xs.length * (rmulCost w + 6 * w + 2) + 8 ∧
      Exec body (integerProducts hQ) (mk v S) m
        (mk v' { S with R := (Function.update (counterR 0 w S.R) (cr .out)
          (cstream A w (List.zipWith (· * ·) xs as) ++ S.R (cr .out))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepare_exec_of_width (body := body) 0 w hw (by omega)
    v S hqR hwR (by
      intro k hk
      exact (hc ⟨k.val, by omega⟩).2)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hwork _ (by decide))
  let SP : Stacks 117 A := { S with R := counterR 0 w S.R }
  have hready : Ready (fun r => SP.R (cr r)) w 0 := counterR_ready_of_work 0 w S.R hwork
  have hclean : CClean mul SP := by
    intro i
    refine ⟨(hc i).1, ?_⟩
    simpa [SP, counterR, (cr_mul .wn i).symm, (cr_mul .pn i).symm,
      (cr_mul .nn i).symm] using (hc i).2
  have hoperand (r : CR) (hr : r ∈ [CR.xs, .ys, .out, .xsv, .ysv, .acc]) :
      SP.R (cr r) = S.R (cr r) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SP, counterR, cr_injective.eq_iff]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := realWeightStream_exec_of_fits (body := body)
    cr_injective cr_mul mul_injective (by decide) hQ hA (by omega) (by omega : 0 ≤ w)
    xs as hlen hxs has v₁ SP hclean hready
    (by rw [hoperand .xs (by simp)]; exact hx)
    (by rw [hoperand .ys (by simp)]; exact hy)
    (by rw [hoperand .xsv (by simp)]; exact hwork _ (by decide))
    (by rw [hoperand .ysv (by simp)]; exact hwork _ (by decide))
    (by rw [hoperand .acc (by simp)]; exact hwork _ (by decide))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, ?_⟩
  simpa only [integerProducts, tdivN_precision_zero, hoperand .out (by simp)] using
    Exec.seq he₁ he₂

end ScalarPlacement

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
