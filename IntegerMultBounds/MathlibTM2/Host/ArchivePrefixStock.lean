module

public import IntegerMultBounds.MathlibTM2.Host.AppendRuns

/-! Advancing a prefix into a reversed restoration archive preserves stock.
Only the appended result contributes retained volume at iteration boundaries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

theorem mn_archive_prefix_size (source archive : Fin T) (hne : source ≠ archive)
    (v w : HS T Q A U) (S : Stacks T A) (xs tail : List (Fin (A+4)))
    (hsource : S.R source = xs++tail) :
    mnSize (mk w {S with R := (Function.update (Function.update S.R source tail)
      archive (xs.reverse++S.R archive))}) = mnSize (mk v S) := by
  let F : Stacks T A := {S with R := Function.update S.R source tail}
  have h₁ : mnSize (mk v F)+(S.R source).length = mnSize (mk v S)+tail.length := by
    simpa only [F,mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt source) tail
  have h₂ : mnSize (mk w {F with R := Function.update F.R archive (xs.reverse++S.R archive)})+
      (F.R archive).length = mnSize (mk v F)+(xs.reverse++S.R archive).length := by
    simpa only [mk,update_rt,get_rt] using
      mn_size_update (mk v F) w (.rt archive) (xs.reverse++S.R archive)
  have hFa : F.R archive = S.R archive := Function.update_of_ne hne.symm _ _
  rw [hFa,List.length_append,List.length_reverse] at h₂
  have hlen := congrArg List.length hsource
  simp only [List.length_append] at hlen
  change mnSize (mk w {F with R := Function.update F.R archive (xs.reverse++S.R archive)}) = _
  omega

theorem mn_archive_prefix_append_size (source archive result : Fin T)
    (hreg : [source,archive,result].Nodup) (v w : HS T Q A U) (S : Stacks T A)
    (xs tail ys : List (Fin (A+4))) (hsource : S.R source = xs++tail) :
    mnSize (mk w {S with R := (Function.update (Function.update (Function.update S.R source tail)
      archive (xs.reverse++S.R archive)) result (ys++S.R result))}) = mnSize (mk v S)+ys.length := by
  have hsa : source ≠ archive := by intro h; subst archive; simp at hreg
  have hsr : source ≠ result := by intro h; subst result; simp at hreg
  have har : archive ≠ result := by intro h; subst result; simp at hreg
  let G : Stacks T A := {S with R := (Function.update (Function.update S.R source tail)
    archive (xs.reverse++S.R archive))}
  have hs := mn_archive_prefix_size source archive hsa v v S xs tail hsource
  have hr : G.R result = S.R result := by simp [G,hsr.symm,har.symm]
  have hb := mn_appendR_size v w G result ys
  rw [hr] at hb
  change mnSize (mk v G) = mnSize (mk v S) at hs
  rw [hs] at hb
  exact hb

end IntegerMultBounds.MathlibTM2.Host
