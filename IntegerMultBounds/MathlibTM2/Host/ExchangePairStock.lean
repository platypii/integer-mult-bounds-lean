module

public import IntegerMultBounds.MathlibTM2.Host.AppendRuns

/-! Replacing two consumed prefixes by two equally sized archive prefixes
preserves stock, independently of the source suffixes and accumulated archives. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type}

theorem mn_exchange_pair_size (source₁ source₂ archive₁ archive₂ : Fin T)
    (hreg : [source₁,source₂,archive₁,archive₂].Nodup)
    (v w : HS T Q A U) (S : Stacks T A)
    (xs ys us vs tail₁ tail₂ : List (Fin (A+4)))
    (hsource₁ : S.R source₁ = xs++tail₁) (hsource₂ : S.R source₂ = ys++tail₂)
    (hu : us.length = xs.length) (hv : vs.length = ys.length) :
    mnSize (mk w {S with R := (Function.update (Function.update (Function.update (Function.update S.R
      source₁ tail₁) source₂ tail₂) archive₁ (us++S.R archive₁)) archive₂ (vs++S.R archive₂))}) = mnSize (mk v S) := by
  have : source₁ ≠ source₂ := by intro he; subst source₂; simp at hreg
  have : source₁ ≠ archive₁ := by intro he; subst archive₁; simp at hreg
  have : source₁ ≠ archive₂ := by intro he; subst archive₂; simp at hreg
  have : source₂ ≠ archive₁ := by intro he; subst archive₁; simp at hreg
  have : source₂ ≠ archive₂ := by intro he; subst archive₂; simp at hreg
  have : archive₁ ≠ archive₂ := by intro he; subst archive₂; simp at hreg
  let F₁ : Stacks T A := {S with R := Function.update S.R source₁ tail₁}
  let F₂ : Stacks T A := {F₁ with R := Function.update F₁.R source₂ tail₂}
  let F₃ : Stacks T A := {F₂ with R := Function.update F₂.R archive₁ (us++F₂.R archive₁)}
  have h₁ : mnSize (mk v F₁)+(S.R source₁).length = mnSize (mk v S)+tail₁.length := by
    simpa only [F₁,mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt source₁) tail₁
  have h₂ : mnSize (mk v F₂)+(S.R source₂).length = mnSize (mk v F₁)+tail₂.length := by
    have hh : mnSize (mk v F₂)+(F₁.R source₂).length = mnSize (mk v F₁)+tail₂.length := by
      simpa only [F₂,mk,update_rt,get_rt] using mn_size_update (mk v F₁) v (.rt source₂) tail₂
    have he : F₁.R source₂ = S.R source₂ := Function.update_of_ne ‹source₁ ≠ source₂›.symm _ _
    rw [he] at hh
    exact hh
  have h₃ := mn_appendR_size v v F₂ archive₁ us
  change mnSize (mk v F₃) = mnSize (mk v F₂)+us.length at h₃
  have h₄ := mn_appendR_size v w F₃ archive₂ vs
  have he : {F₃ with R := Function.update F₃.R archive₂ (vs++F₃.R archive₂)} =
      {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        source₁ tail₁) source₂ tail₂) archive₁ (us++S.R archive₁)) archive₂ (vs++S.R archive₂))} := by
    simp [F₃,F₂,F₁,‹source₁ ≠ archive₁›.symm,‹source₂ ≠ archive₁›.symm,
      ‹source₁ ≠ archive₂›.symm,‹source₂ ≠ archive₂›.symm,‹archive₁ ≠ archive₂›.symm]
  rw [he] at h₄
  rw [hsource₁,List.length_append] at h₁
  rw [hsource₂,List.length_append] at h₂
  omega

end IntegerMultBounds.MathlibTM2.Host
