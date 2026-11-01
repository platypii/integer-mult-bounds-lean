module

public import IntegerMultBounds.MathlibTM2.Fast.BandLine
public import IntegerMultBounds.MathlibTM2.Host.ReplaceThreeStock

/-! A completed forward column releases its coefficient column. Pending-word
replacement preserves length, and moving its head to the output preserves stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type} {rg : RsbR → Fin T}

theorem bandFwdStep_stock (hrg : Function.Injective rg) (v v' : HS T Q A U)
    (S : Stacks T A) (w : ℕ) (y : GaussianInt)
    (rs next more col cols : List GaussianInt) (hlen : next.length = rs.length)
    (hvk : S.R (rg .vk) = cstream A w (y::(rs++more)))
    (hef : S.R (rg .ef) = cstream A w (col++cols)) :
    mnSize (mk v' {S with R := (Function.update (Function.update (Function.update S.R
      (rg .vk) (cstream A w (next++more))) (rg .ef) (cstream A w cols))
      (rg .dout) (csyms A w y++S.R (rg .dout)))})+col.length*w = mnSize (mk v S) := by
  have h := mn_replace_three_size (rg .vk) (rg .ef) (rg .dout)
    (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide)) v v' S
    (cstream A w (next++more)) (cstream A w cols) (csyms A w y++S.R (rg .dout))
  rw [hvk,hef] at h
  simp only [length_cstream,List.length_cons,List.length_append,length_csyms,hlen] at h
  nlinarith only [h]

/-- The same balance applies to the physical state returned by the band contract. -/
theorem bandFwdStep_stock_of_holds (hrg : Function.Injective rg) (v v' : HS T Q A U)
    (S F : Stacks T A) (w : ℕ) (y : GaussianInt)
    (rs next more col cols : List GaussianInt) (hlen : next.length = rs.length)
    (hvk : S.R (rg .vk) = cstream A w (y::(rs++more)))
    (hef : S.R (rg .ef) = cstream A w (col++cols))
    (hframe : RsbFr rg S F)
    (hholds : RsbHolds rg F (Function.update (Function.update (Function.update
      (fun r => S.R (rg r)) .vk (cstream A w (next++more))) .ef (cstream A w cols))
      .dout (csyms A w y++S.R (rg .dout)))) :
    mnSize (mk v' F)+col.length*w = mnSize (mk v S) := by
  have hF : F = {S with R := (Function.update (Function.update (Function.update S.R
      (rg .vk) (cstream A w (next++more))) (rg .ef) (cstream A w cols))
      (rg .dout) (csyms A w y++S.R (rg .dout)))} := by
    refine Stacks.ext hframe.1 hframe.2.1 hframe.2.2.1 ?_
    funext k
    by_cases hk : ∃ r, rg r = k
    · obtain ⟨r,rfl⟩ := hk
      simpa only [Function.update_apply,hrg.eq_iff] using hholds r
    · have hnot : ∀ r, rg r ≠ k := by simpa using hk
      simp only [Function.update_of_ne (hnot .dout).symm,
        Function.update_of_ne (hnot .ef).symm,Function.update_of_ne (hnot .vk).symm]
      exact hframe.2.2.2 k hnot
  rw [hF]
  exact bandFwdStep_stock hrg v v' S w y rs next more col cols hlen hvk hef

/-- A reciprocal replacement keeps the pending stack's length and consumes one table word. -/
theorem bandRecip_stock (hrg : Function.Injective rg) (v v' : HS T Q A U)
    (S : Stacks T A) (w : ℕ) (x y r : GaussianInt) (pending table : List (Fin (A+4)))
    (hvk : S.R (rg .vk) = csyms A w x++pending)
    (htb : S.R (rg .tb) = csyms A w r++table) :
    mnSize (mk v' {S with R := (Function.update (Function.update S.R
      (rg .vk) (csyms A w y++pending)) (rg .tb) table)})+w = mnSize (mk v S) := by
  have h := mn_replace_three_size (rg .vk) (rg .tb) (rg .dout)
    (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide)) v v' S
    (csyms A w y++pending) table (S.R (rg .dout))
  have he : Function.update (Function.update (Function.update S.R
      (rg .vk) (csyms A w y++pending)) (rg .tb) table) (rg .dout) (S.R (rg .dout)) =
      Function.update (Function.update S.R (rg .vk) (csyms A w y++pending)) (rg .tb) table := by
    apply Function.update_eq_self_iff.mpr
    simp [hrg.eq_iff]
  rw [he,hvk,htb] at h
  simp only [List.length_append,length_csyms] at h
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
