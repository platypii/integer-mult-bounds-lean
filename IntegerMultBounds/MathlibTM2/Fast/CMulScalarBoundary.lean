module

public import IntegerMultBounds.MathlibTM2.Fast.CMulStream
public import IntegerMultBounds.MathlibTM2.Host.ArchivePrefixStock

/-! A scalar-table boundary moves consumed coefficients into their restoration
archive. Only the retained result contributes additional simultaneous stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {U : Type} {cr : CR → Fin T}

def scalarLoopSt (ρ : CR → List (Fin (A+4))) (w : ℕ) (g : GaussianInt → GaussianInt)
    (rem done : List GaussianInt) : CR → List (Fin (A+4)) :=
  Function.update (Function.update (Function.update ρ .xs (cstream A w rem))
    .xsv ((cstream A w done).reverse++ρ .xsv)) .acc ((cstream A w (done.map g)).reverse++ρ .acc)

def scalarBoundary (cr : CR → Fin T) (S : Stacks T A) (w : ℕ) (g : GaussianInt → GaussianInt)
    (rem done : List GaussianInt) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update S.R (cr .xs) (cstream A w rem))
    (cr .xsv) ((cstream A w done).reverse++S.R (cr .xsv)))
    (cr .acc) ((cstream A w (done.map g)).reverse++S.R (cr .acc)))}

theorem scalarBoundary_holds (hcr : Function.Injective cr) (S : Stacks T A)
    (w : ℕ) (g : GaussianInt → GaussianInt) (rem done : List GaussianInt) :
    CHolds cr (scalarBoundary cr S w g rem done) (scalarLoopSt (fun r => S.R (cr r)) w g rem done) := by
  intro r
  simp only [scalarBoundary,scalarLoopSt,upd_comp hcr]

theorem scalarBoundary_fr (S : Stacks T A) (w : ℕ) (g : GaussianInt → GaussianInt)
    (rem done : List GaussianInt) : CFr cr S (scalarBoundary cr S w g rem done) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  intro k hk
  simp [scalarBoundary,(hk .xs).symm,(hk .xsv).symm,(hk .acc).symm]

theorem CFr.eq_of_holds {S F G : Stacks T A} (hf : CFr cr S F) (hg : CFr cr S G)
    (hh : ∀ r, F.R (cr r) = G.R (cr r)) : F = G := by
  ext1
  · exact hf.1.trans hg.1.symm
  · exact hf.2.1.trans hg.2.1.symm
  · exact hf.2.2.1.trans hg.2.2.1.symm
  · funext k
    by_cases hk : ∃ r, cr r = k
    · obtain ⟨r,rfl⟩ := hk
      exact hh r
    · have hnot : ∀ r, cr r ≠ k := by simpa using hk
      exact (hf.2.2.2 k hnot).trans (hg.2.2.2 k hnot).symm

theorem scalarBoundary_size (hcr : Function.Injective cr) (v vf : HS T Q A U) (S : Stacks T A)
    (w : ℕ) (g : GaussianInt → GaussianInt) (xs rem done : List GaussianInt)
    (hsrc : S.R (cr .xs) = cstream A w xs) (hparts : done++rem = xs) :
    mnSize (mk vf (scalarBoundary cr S w g rem done)) = mnSize (mk v S)+done.length*w := by
  have hnd : [cr .xs,cr .xsv,cr .acc].Nodup := by
    exact (show [CR.xs,CR.xsv,CR.acc].Nodup by decide).map hcr
  have hb := mn_archive_prefix_append_size (cr .xs) (cr .xsv) (cr .acc) hnd v vf S
    (cstream A w done) (cstream A w rem) ((cstream A w (done.map g)).reverse)
    (by rw [← cstream_append,hparts]; exact hsrc)
  simpa only [scalarBoundary,List.length_reverse,length_cstream,List.length_map] using hb

end IntegerMultBounds.MathlibTM2.Fast
