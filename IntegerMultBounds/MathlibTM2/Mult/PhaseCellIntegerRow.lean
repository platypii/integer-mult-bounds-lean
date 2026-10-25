module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntegerMultiply
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowAccumulator

/-! # Executed integer generator-row arithmetic

The existing 117-tape bank multiplies aligned integer operands and subtracts
their products from a stored RHS word. All readiness is generated and paid.
Operand staging, iteration control and coefficient generation remain separate.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

/-- Arithmetic-only row call; installed counters are preserved for the next row. -/
noncomputable def integerRowPrepared (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq (realWeightStream cr mul mul_injective (by decide) hQ) (subtractRow 96 (cr .out) 97 94 98)

noncomputable def integerRow (hQ : SS.states ≤ Q) : Pr P 117 Q A U :=
  .seq prepare (integerRowPrepared hQ)

theorem integerRowPrepared_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w : ℕ} (hw : 1 ≤ w) (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (rhs : GaussianInt) (hc : CClean mul S)
    (hready : Ready (fun r => S.R (cr r)) w 0)
    (hwork : ∀ r ∈ [CR.xsv, .ysv, .acc, .out], S.R (cr r) = []) (hwR : (S.R 94).length = w)
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w as)
    (hrhs : S.R 96 = csyms A w rhs) (hsaved : S.R 97 = []) (htmp : S.R 98 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ xs.length * (rmulCost w + 13 * w + 12) + 10 ∧
      Exec body (integerRowPrepared hQ) (mk v S) m
        (mk v' { S with R := (Function.update S.R 96
          (csyms A w (rhs - (List.zipWith (· * ·) xs as).sum))) }) := by
  let products := List.zipWith (· * ·) xs as
  have hplen : products.length = xs.length := by simp [products, hlen]
  have hout : S.R (cr .out) = [] := hwork _ (by simp)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := realWeightStream_exec_of_fits (body := body)
    cr_injective cr_mul mul_injective (by decide) hQ hA hw (by omega : 0 ≤ w)
    xs as hlen hxs has v S hc hready hx hy (hwork _ (by simp)) (hwork _ (by simp)) (hwork _ (by simp))
  have he₁' := he₁
  simp only [tdivN_precision_zero] at he₁'
  let S₁ : Stacks 117 A := { S with R := (Function.update S.R (cr .out)
    (cstream A w products ++ S.R (cr .out))) }
  obtain ⟨v₂, hu₂, he₂⟩ := subtractRow_exec (body := body) (w := w)
    (show [(96 : Fin 117), cr .out, 97, 94, 98].Nodup by decide) hA (by omega) products v₁ S₁ rhs
    (by simpa [S₁, cr, OutputPlacement.code] using hrhs)
    (by simp [S₁, hout])
    (by simpa [S₁, cr, OutputPlacement.code] using hsaved)
    (by simpa [S₁, cr, OutputPlacement.code] using hwR)
    (by simpa [S₁, cr, OutputPlacement.code] using htmp)
  refine ⟨v₂, m₁ + (products.length * (7 * w + 10) + 2), hu₂.trans hu₁, ?_,
    (Exec.seq he₁' he₂).cast rfl ?_⟩
  · rw [hplen]
    nlinarith only [hm₁]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ha : k = 96
    · subst k; simp [products]
    by_cases ho : k = cr .out
    · subst k
      simpa [S₁, cr, OutputPlacement.code] using hout.symm
    simp [S₁, ha, ho]


theorem integerRow_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w : ℕ} (hw : 5 ≤ w) (xs as : List GaussianInt) (hlen : xs.length = as.length)
    (hxs : ∀ x ∈ xs, Fits w x) (has : ∀ a ∈ as, Fits w a ∧ a.im = 0)
    (v : HS 117 Q A U) (S : Stacks 117 A) (rhs : GaussianInt) (hc : CClean mul S)
    (hwork : ∀ r, r ∉ [CR.xs, .ys] → S.R (cr r) = [])
    (hqR : (S.R 100).length = 0) (hwR : (S.R 94).length = w)
    (hx : S.R (cr .xs) = cstream A w xs) (hy : S.R (cr .ys) = cstream A w as)
    (hrhs : S.R 96 = csyms A w rhs) (hsaved : S.R 97 = []) (htmp : S.R 98 = []) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ prepareCost 0 w + xs.length * (rmulCost w + 13 * w + 12) + 10 ∧
      Exec body (integerRow hQ) (mk v S) m
        (mk v' { S with R := (Function.update (counterR 0 w S.R) 96
          (csyms A w (rhs - (List.zipWith (· * ·) xs as).sum))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := prepare_exec_of_width (body := body) 0 w hw (by omega)
    v S hqR hwR (by
      intro k hk
      exact (hc ⟨k.val, by omega⟩).2)
    (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> exact hwork _ (by decide))
  let SP : Stacks 117 A := { S with R := counterR 0 w S.R }
  have hready : Ready (fun r => SP.R (cr r)) w 0 :=
    counterR_ready_of_work 0 w S.R (fun r hr => hwork r (by
      intro hh
      exact hr (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh ⊢
        exact hh.elim Or.inl (fun h => Or.inr (Or.inl h)))))
  have hclean : CClean mul SP := by
    intro i
    refine ⟨(hc i).1, ?_⟩
    simpa [SP, counterR, (cr_mul .wn i).symm, (cr_mul .pn i).symm,
      (cr_mul .nn i).symm] using (hc i).2
  have hports (r : CR) (hr : r ∈ [CR.xs, .ys, .xsv, .ysv, .acc, .out]) :
      SP.R (cr r) = S.R (cr r) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SP, counterR, cr_injective.eq_iff]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := integerRowPrepared_exec (body := body) hQ hA (by omega : 1 ≤ w)
    xs as hlen hxs has v₁ SP rhs hclean hready
    (by
      intro r hr
      rw [hports r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        exact Or.inr (Or.inr hr))]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact hwork _ (by decide))
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hwR)
    (by rw [hports .xs (by simp)]; exact hx)
    (by rw [hports .ys (by simp)]; exact hy)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hrhs)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using hsaved)
    (by simpa [SP, counterR, cr, OutputPlacement.code] using htmp)
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
