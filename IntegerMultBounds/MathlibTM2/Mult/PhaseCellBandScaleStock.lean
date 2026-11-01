module

public import IntegerMultBounds.MathlibTM2.Fast.BandLineDriver
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStreamStock

/-! Boundary scaling reuses the scalar stream's one numerical reserve.
Retiring the restored input is a zero-push operation and adds no peak stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem bandScaleP_exec_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {x y o : RsbR} (hfree : RsbFree x y o) {w q : ℕ} (hw : 1 ≤ w) (hq : q ≤ w)
    (xs : List GaussianInt) (c : ℤ) (hxs : ∀ z ∈ xs, Fits w z) (hc : Fits w (⟨c,0⟩ : GaussianInt))
    (v : HS T Q A U) (S : Stacks T A) (hclean : RsbClean ι S)
    (hr : RsbReady (fun r => S.R (rg r)) w q)
    (hx : S.R (rg x) = cstream A w xs) (hy : S.R (rg y) = csyms A w (⟨c,0⟩ : GaussianInt))
    (ho : S.R (rg o) = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ xs.length*(rmulCost w+6*w+8)+6+(2*(xs.length*w)+2) ∧
      ∀ C, mnProgPush (cmulBlock (rsbCr rg x y o)
        (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ (rsbCr rg x y o))) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+realScalarWorkspace C w xs.length)
        depth (bandScaleP rg hι hT hQ x y o) (mk v S) n
        (mk v' {S with R := Function.update (Function.update S.R (rg o)
          (cstream A w (xs.map fun z => tdivN q (z*⟨c,0⟩)))) (rg x) []}) := by
  let cr := rsbCr rg x y o
  have hcr : Function.Injective cr := hrg.comp (rsbRemap_injective hfree)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := realScalarStream_exec_within (body := body) hcr
    (fun r j => hdisj (rsbRemap x y o r) j) hι hT hQ hA hw hq xs (⟨c,0⟩ : GaussianInt) hxs hc rfl
    v S (fun j => ⟨hclean.1 (ι j),hclean.2 j⟩) (hr.ready x y o) hx hy
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    (hr.empty _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  let M : Stacks T A := {S with R := (Function.update S.R (rg o)
    (cstream A w (xs.map fun z => tdivN q (z*⟨c,0⟩))))}
  obtain ⟨v₂,hu₂,he₂⟩ := emptyR_exec body (rg x) v₁ M
  have hlen : (M.R (rg x)).length = xs.length*w := by
    simp [M,hrg.eq_iff,hfree.2.1,hx,length_cstream]
  refine ⟨v₂,n₁+(2*(M.R (rg x)).length+2),hu₂.trans hu₁,?_,?_⟩
  · rw [hlen]
    omega
  · intro C hpush depth
    have ht₁ := he₁ C hpush depth
    have ht₁' : ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+realScalarWorkspace C w xs.length) depth
        (realScalarStream cr ι hι hT hQ) (mk v S) n₁ (mk v₁ M) := by
      have hout : S.R (cr .out) = [] := ho
      simp only [hout,List.append_nil] at ht₁
      exact ht₁
    have ht₂ := mn_native_exec_within he₂ 0 (by
      simp [emptyR,emptyStep,whileR,peekR,mnNativePushBound,mnActPush]) depth
      (mnSize (mk v₁ M)+depth) (by simp)
    have hsize := ht₁'.final
    exact .seq ht₁' (ht₂.mono (by intro d z hz; omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
