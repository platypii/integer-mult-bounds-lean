module

public import IntegerMultBounds.MathlibTM2.Routing.HaloAxisTensorInvariant
public import IntegerMultBounds.MathlibTM2.Routing.TensorFiberLayout
public import IntegerMultBounds.MathlibTM2.Routing.HaloAxisFromDimensions

/-! Exact stored input and output of a target-halo axis. Tabulation makes the
logical invariant an equality of actual nested lists, hence of encoded tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloAxisTensorLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Routing
  HaloPassContext RectangularHaloCoordinates RetainedHaloTensor HaloAxisTensorInvariant
variable {ι : Type} [DecidableEq ι]

def layout (P N B M : ℕ) (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (base : ℕ → ℕ → ι → ℕ × ℕ) (f : (ι → ℕ) → GaussianInt) :=
  TensorFiberLayout.tabulate P N B M fun a k b t =>
    pullback axis retained f (Function.update (base a b) i (k,t))

theorem layout_shape (p : Parameters) (P : ℕ) (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (base : ℕ → ℕ → ι → ℕ × ℕ) (f : (ι → ℕ) → GaussianInt) :
    ∀ matrices ∈ layout P p.N p.B p.L axis retained i base f, HaloPassContext.Shape p matrices := by
  intro matrices hm
  have h := (TensorFiberLayout.tabulate_shape P p.N p.B p.L
    (fun a k b t => pullback axis retained f (Function.update (base a b) i (k,t)))).2 matrices hm
  exact ⟨h.1,fun rows hr => (h.2 rows hr).1,fun rows hr => (h.2 rows hr).2⟩

theorem transform_layout (p : Parameters) (P : ℕ) (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (hi : i ∉ retained) (haxis : axis i = axisOf p)
    (base : ℕ → ℕ → ι → ℕ × ℕ) (f : (ι → ℕ) → GaussianInt) :
    HaloAxisCoordinates.transform p (layout P p.N p.B p.L axis retained i base f) =
      layout P p.N p.B (p.L+2*p.H) axis (insert i retained) i base f := by
  have hshape := layout_shape p P axis retained i base f
  have hlen : (layout P p.N p.B p.L axis retained i base f).length = P := by simp [layout,TensorFiberLayout.tabulate]
  apply TensorFiberLayout.eq_tabulate (0 : GaussianInt)
  · have hs := HaloAxisCoordinates.transform_shape p _ hshape
    exact ⟨hs.1.trans hlen,hs.2⟩
  · intro a ha k hk b hb t ht
    apply transform_pullback p axis retained i hi haxis f base _ hshape
      (fun a ha k hk b hb t ht => TensorFiberLayout.tabulate_entry 0 P p.N p.B p.L _ a k b t
        (hlen ▸ ha) hk hb ht) a (hlen.symm ▸ ha) k hk b hb t ht

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main

/-- Actual execution on the canonical stored tensor, with the enlarged retained
layout named explicitly in the endpoint. Derived headers are generated and
retired; only ordinary dimensions and exponents are retained inputs. -/
theorem run_exec {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}
    (p : Parameters) (P : ℕ) (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (hi : i ∉ retained) (haxis : axis i = axisOf p)
    (base : ℕ → ℕ → ι → ℕ × ℕ) (f : (ι → ℕ) → GaussianInt)
    (hA : 4 ≤ A) (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hm : HaloPassHeaderSetup.Masters p S) (hf : Fresh S) (hprefix : (S.R 64).length = P)
    (hblank : ∀ j ∈ HaloPassHeaderSetup.blank ++ [(56 : Fin 117),59,60,61,62,63], S.R j = [])
    (hsrc : S.R 39 = (layout P p.N p.B p.L axis retained i base f).flatMap (input A p)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ HaloAxisFromDimensions.cost p P ∧
      Exec body HaloAxisFromDimensions.run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          ((layout P p.N p.B (p.L+2*p.H) axis (insert i retained) i base f).flatMap (input A p)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+HaloAxisFromDimensions.reserve p P)
        depth HaloAxisFromDimensions.run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          ((layout P p.N p.B (p.L+2*p.H) axis (insert i retained) i base f).flatMap (input A p)++tail))})) := by
  have hlen : (layout P p.N p.B p.L axis retained i base f).length = P := by
    simp [layout,TensorFiberLayout.tabulate]
  obtain ⟨vf,n,hu,hn,he,hs⟩ := HaloAxisFromDimensions.run_exec (body := body) p
    (layout P p.N p.B p.L axis retained i base f) (layout_shape p P axis retained i base f)
    hA tail v S hm hf (hprefix.trans hlen.symm) hblank hsrc
  rw [transform_layout p P axis retained i hi haxis base f] at he hs
  exact ⟨vf,n,hu,by simpa only [hlen] using hn,he,by simpa only [hlen] using hs⟩

end IntegerMultBounds.MathlibTM2.Routing.HaloAxisTensorLayout
