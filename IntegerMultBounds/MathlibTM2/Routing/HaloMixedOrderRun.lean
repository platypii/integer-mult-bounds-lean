module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedOrder

/-! Actual movement between the manuscript's mixed order and the halo pass's
suffix view. The same statements apply after the local width has enlarged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMixedOrderRun
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  RetainedHaloTensor RetainedTensorEnumeration HaloMixedOrder
variable {ι : Type} [DecidableEq ι]
variable {T Q A : ℕ} {J U : Type} {body : J → Pr J T Q A U}

def moveVolume (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι) (k w : ℕ) :=
  ((moveBefore left i right).map (width axis retained)).prod*
    (((moveMiddle right).map (width axis retained)).prod*(2^k*w))

theorem toSuffix_exec (r : Fin 16 → Fin T) (hr : Function.Injective r)
    (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (w k : ℕ) (hw : 0 < w) (hfit : localLength axis retained i ≤ 2^k)
    (f : (ι → ℕ) → GaussianInt) (zero : Fin (A+4)) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hh : FieldOrderRun.Headers r k ((moveBefore left i right).map (width axis retained)).prod
      ((moveMiddle right).map (width axis retained)).prod (localLength axis retained i) w S)
    (hf : ∀ j ∈ FieldOrderRun.scratch, S.R (r j) = [])
    (hsrc : S.R (r 11) = RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A w)++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(64*moveVolume axis retained left i right k w+3)+
        384*moveVolume axis retained left i right k w+2 ∧
      Exec body (FieldOrderRun.backward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (HaloCoordinateAxis.source A w axis retained (haloBefore left) (haloMiddle left right) i f++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          1000*moveVolume axis retained left i right k w) depth (FieldOrderRun.backward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (HaloCoordinateAxis.source A w axis retained (haloBefore left) (haloMiddle left right) i f++tail))})) := by
  obtain ⟨vf,n,hu,hcost,he,hs⟩ := CoordinateFieldRun.backward_exec (body := body) r hr
    (width axis retained) (moveBefore left i right) (moveMiddle right) [] (.inr i) (fields_fresh left i right hn).1
    (fun _ => 0) w k (fun coords => csyms A w (pullback axis retained f (unpack coords)))
    (by intro coords; simp [csyms]) (product_pos axis retained _) (product_pos axis retained _)
    (by simpa using hw) hfit zero tail v S (by simpa only [width,List.map_nil,List.prod_nil,Nat.one_mul] using hh) hf (by rw [←mixed_stream]; exact hsrc)
  simp only [List.map_nil,List.prod_nil,Nat.one_mul] at hcost he hs
  rw [←suffix_stream A w axis retained left i right f] at he hs
  exact ⟨vf,n,hu,hcost,he,hs⟩

theorem fromSuffix_exec (r : Fin 16 → Fin T) (hr : Function.Injective r)
    (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (w k : ℕ) (hw : 0 < w) (hfit : localLength axis retained i ≤ 2^k)
    (f : (ι → ℕ) → GaussianInt) (zero : Fin (A+4)) (tail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hh : FieldOrderRun.Headers r k ((moveBefore left i right).map (width axis retained)).prod
      ((moveMiddle right).map (width axis retained)).prod (localLength axis retained i) w S)
    (hf : ∀ j ∈ FieldOrderRun.scratch, S.R (r j) = [])
    (hsrc : S.R (r 11) = HaloCoordinateAxis.source A w axis retained (haloBefore left) (haloMiddle left right) i f++tail) :
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(60*moveVolume axis retained left i right k w+3)+
        384*moveVolume axis retained left i right k w+2 ∧
      Exec body (FieldOrderRun.forward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A w)++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          1000*moveVolume axis retained left i right k w) depth (FieldOrderRun.forward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A w)++tail))})) := by
  obtain ⟨vf,n,hu,hcost,he,hs⟩ := CoordinateFieldRun.forward_exec (body := body) r hr
    (width axis retained) (moveBefore left i right) (moveMiddle right) [] (.inr i) (fields_fresh left i right hn).1
    (fun _ => 0) w k (fun coords => csyms A w (pullback axis retained f (unpack coords)))
    (by intro coords; simp [csyms]) (product_pos axis retained _) (product_pos axis retained _)
    (by simpa using hw) hfit zero tail v S (by simpa only [width,List.map_nil,List.prod_nil,Nat.one_mul] using hh) hf (by rw [←suffix_stream]; exact hsrc)
  simp only [List.map_nil,List.prod_nil,Nat.one_mul] at hcost he hs
  rw [←mixed_stream A w axis retained left i right f] at he hs
  exact ⟨vf,n,hu,hcost,he,hs⟩

end IntegerMultBounds.MathlibTM2.Routing.HaloMixedOrderRun
