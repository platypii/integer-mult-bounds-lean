module

public import IntegerMultBounds.MathlibTM2.Routing.HaloCoordinateLayout

/-! The complete generated-header halo pass on the actual enumerated tensor
stream, with prefix and spectator bases derived from their field lists. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloCoordinateAxis
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  RetainedHaloTensor RetainedTensorEnumeration HaloPassContext HaloAxisTensorInvariant HaloCoordinateLayout
variable {ι : Type} [DecidableEq ι]
variable {Q A : ℕ} {J U : Type} {body : J → Pr J 117 Q A U}

def source (A w : ℕ) (axis : ι → Axis) (retained : Finset ι) (before middle : List (Sum ι ι))
    (i : ι) (f : (ι → ℕ) → GaussianInt) :=
  CoordinateFieldLayout.stream (width axis retained) (before++Sum.inl i::(middle++[Sum.inr i]))
    (fun _ => 0) (fun coords => csyms A w (pullback axis retained f (unpack coords)))

theorem run_exec (p : Parameters) (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (hi : i ∉ retained) (haxis : axis i = axisOf p)
    (before middle : List (Sum ι ι)) (hc : Sum.inl i ∉ middle)
    (hb : Sum.inr i ∉ before) (hmiddle : Sum.inr i ∉ middle)
    (hB : (middle.map (width axis retained)).prod = p.B) (f : (ι → ℕ) → GaussianInt)
    (hA : 4 ≤ A) (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hm : HaloPassHeaderSetup.Masters p S) (hf : Fresh S)
    (hprefix : (S.R 64).length = (before.map (width axis retained)).prod)
    (hblank : ∀ j ∈ HaloPassHeaderSetup.blank ++ [(56 : Fin 117),59,60,61,62,63], S.R j = [])
    (hsrc : S.R 39 = source A p.w axis retained before middle i f++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ HaloAxisFromDimensions.cost p (before.map (width axis retained)).prod ∧
      Exec body HaloAxisFromDimensions.run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          (source A p.w axis (insert i retained) before middle i f++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          HaloAxisFromDimensions.reserve p (before.map (width axis retained)).prod)
        depth HaloAxisFromDimensions.run (mk v S) n
        (mk vf {S with R := (Function.update S.R 39
          (source A p.w axis (insert i retained) before middle i f++tail))})) := by
  have hN : (axis i).N = p.N := by simp only [haxis,axisOf]
  have hL : localLength axis retained i = p.L := by simp [localLength,hi,haxis,axisOf]
  have hM : localLength axis (insert i retained) i = p.L+2*p.H := by simp [localLength,haxis,axisOf]
  have hin := stream_layout A p.w p rfl axis retained i before middle hc p.N p.B p.L hN hB hL f
  have hout := stream_layout A p.w p rfl axis (insert i retained) i before middle hc p.N p.B (p.L+2*p.H)
    hN (by rw [map_width_insert axis retained i middle hmiddle]; exact hB) hM f
  rw [map_width_insert axis retained i before hb,base_insert axis retained i before middle hb hmiddle] at hout
  obtain ⟨vf,n,hu,hn,he,hs⟩ := HaloAxisTensorLayout.run_exec (body := body) p
    (before.map (width axis retained)).prod axis retained i hi haxis (base axis retained before middle) f
    hA tail v S hm hf hprefix hblank (by rw [←hin]; exact hsrc)
  rw [←hout] at he hs
  exact ⟨vf,n,hu,hn,he,hs⟩

end IntegerMultBounds.MathlibTM2.Routing.HaloCoordinateAxis
