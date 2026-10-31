module

public import IntegerMultBounds.MathlibTM2.Fast.CMulScalarBoundary

/-! Both operand streams move into restoration archives without stock growth.
Only the pointwise product accumulator grows at multiplication boundaries. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type} {cr : CR → Fin T}

def pairBoundary (cr : CR → Fin T) (S : Stacks T A) (w : ℕ)
    (g : GaussianInt → GaussianInt → GaussianInt)
    (rem done : List (GaussianInt × GaussianInt)) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update
    S.R (cr .xs) (cstream A w (rem.map Prod.fst))) (cr .ys) (cstream A w (rem.map Prod.snd)))
    (cr .xsv) ((cstream A w (done.map Prod.fst)).reverse++S.R (cr .xsv)))
    (cr .ysv) ((cstream A w (done.map Prod.snd)).reverse++S.R (cr .ysv)))
    (cr .acc) ((cstream A w (done.map fun z => g z.1 z.2)).reverse++S.R (cr .acc)))}

theorem pairBoundary_holds (hcr : Function.Injective cr) (S : Stacks T A) (w : ℕ)
    (g : GaussianInt → GaussianInt → GaussianInt) (rem done : List (GaussianInt × GaussianInt)) :
    CHolds cr (pairBoundary cr S w g rem done)
      (blockLoopSt (fun r => S.R (cr r)) w g [] rem done) := by
  intro r
  simp only [pairBoundary,blockLoopSt,upd_comp hcr,List.append_nil]

theorem pairBoundary_fr (S : Stacks T A) (w : ℕ) (g : GaussianInt → GaussianInt → GaussianInt)
    (rem done : List (GaussianInt × GaussianInt)) : CFr cr S (pairBoundary cr S w g rem done) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro k hk
  simp [pairBoundary,(hk .xs).symm,(hk .ys).symm,(hk .xsv).symm,(hk .ysv).symm,(hk .acc).symm]

theorem pairBoundary_size (hcr : Function.Injective cr) (v vf : HS T Q A U) (S : Stacks T A)
    (w : ℕ) (g : GaussianInt → GaussianInt → GaussianInt)
    (zs rem done : List (GaussianInt × GaussianInt))
    (hx : S.R (cr .xs) = cstream A w (zs.map Prod.fst))
    (hy : S.R (cr .ys) = cstream A w (zs.map Prod.snd)) (hparts : done++rem = zs) :
    mnSize (mk vf (pairBoundary cr S w g rem done)) = mnSize (mk v S)+done.length*w := by
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R (cr .xs)
    (cstream A w (rem.map Prod.fst))) (cr .xsv)
    ((cstream A w (done.map Prod.fst)).reverse++S.R (cr .xsv)))}
  let G : Stacks T A := {F with R := (Function.update (Function.update F.R (cr .ys)
    (cstream A w (rem.map Prod.snd))) (cr .ysv)
    ((cstream A w (done.map Prod.snd)).reverse++F.R (cr .ysv)))}
  have hx' : S.R (cr .xs) = cstream A w (done.map Prod.fst)++cstream A w (rem.map Prod.fst) := by
    rw [← cstream_append,← List.map_append,hparts]; exact hx
  have hy' : F.R (cr .ys) = cstream A w (done.map Prod.snd)++cstream A w (rem.map Prod.snd) := by
    simp only [F,Function.update_of_ne (hcr.ne (by decide : CR.ys ≠ .xsv)),
      Function.update_of_ne (hcr.ne (by decide : CR.ys ≠ .xs))]
    rw [← cstream_append,← List.map_append,hparts]; exact hy
  have hs₁ := mn_archive_prefix_size (cr .xs) (cr .xsv) (hcr.ne (by decide)) v v S _ _ hx'
  have hs₂ := mn_archive_prefix_size (cr .ys) (cr .ysv) (hcr.ne (by decide)) v v F _ _ hy'
  have hs₃ := mn_appendR_size v vf G (cr .acc)
    ((cstream A w (done.map fun z => g z.1 z.2)).reverse)
  change mnSize (mk v F) = mnSize (mk v S) at hs₁
  change mnSize (mk v G) = mnSize (mk v F) at hs₂
  rw [hs₂,hs₁] at hs₃
  have hG : {G with R := (Function.update G.R (cr .acc)
      ((cstream A w (done.map fun z => g z.1 z.2)).reverse++G.R (cr .acc)))} =
      pairBoundary cr S w g rem done := by
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hk : k = cr .acc
    · subst k; simp [G,F,pairBoundary,hcr.eq_iff]
    · simp [G,F,pairBoundary,Function.update_apply,hk]
      split_ifs <;> subst_vars <;> simp_all [hcr.eq_iff]
  rw [hG] at hs₃
  simpa only [List.length_reverse,length_cstream,List.length_map] using hs₃

end IntegerMultBounds.MathlibTM2.Fast
