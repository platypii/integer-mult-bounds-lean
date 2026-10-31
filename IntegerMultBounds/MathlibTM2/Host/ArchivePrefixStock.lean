module

public import IntegerMultBounds.MathlibTM2.Host.AppendRuns

/-! Advancing a prefix into a reversed restoration archive preserves stock.
Only the appended result contributes retained volume at iteration boundaries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

theorem mn_archive_prefix_append_size (source archive result : Fin T)
    (hreg : [source,archive,result].Nodup) (v w : HS T Q A U) (S : Stacks T A)
    (xs tail ys : List (Fin (A+4))) (hsource : S.R source = xs++tail) :
    mnSize (mk w {S with R := (Function.update (Function.update (Function.update S.R source tail)
      archive (xs.reverse++S.R archive)) result (ys++S.R result))}) = mnSize (mk v S)+ys.length := by
  have hsa : source ≠ archive := by intro h; subst archive; simp at hreg
  have hsr : source ≠ result := by intro h; subst result; simp at hreg
  have har : archive ≠ result := by intro h; subst result; simp at hreg
  let F : Stacks T A := {S with R := Function.update S.R source tail}
  let G : Stacks T A := {F with R := Function.update F.R archive (xs.reverse++S.R archive)}
  have h₁ : mnSize (mk v F)+(S.R source).length = mnSize (mk v S)+tail.length := by
    simpa only [F,mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt source) tail
  have h₂ : mnSize (mk v G)+(S.R archive).length =
      mnSize (mk v F)+(xs.length+(S.R archive).length) := by
    have h : mnSize (mk v G)+(F.R archive).length =
        mnSize (mk v F)+(xs.reverse++S.R archive).length := by
      simpa only [G,mk,update_rt,get_rt] using
        mn_size_update (mk v F) v (.rt archive) (xs.reverse++S.R archive)
    have hFa : F.R archive = S.R archive := Function.update_of_ne hsa.symm _ _
    simpa only [hFa,List.length_append,List.length_reverse] using h
  have hresult : G.R result = S.R result := by
    simp [G,F,hsr.symm,har.symm]
  have h₃ := mn_appendR_size v w G result ys
  rw [hresult] at h₃
  have hlen := congrArg List.length hsource
  simp only [List.length_append] at hlen
  change mnSize (mk w {G with R := Function.update G.R result (ys++S.R result)}) = _
  omega

end IntegerMultBounds.MathlibTM2.Host
