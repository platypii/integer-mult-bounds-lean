module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMixedOrderRun

/-! Expose contiguous local fields from the actual mixed retained archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RetainedFieldRun
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  RetainedHaloTensor RetainedTensorEnumeration HaloMixedOrder
variable {ι : Type} [DecidableEq ι]

def archive (A w : ℕ) (axis : ι → Axis) (retained : Finset ι)
    (fields : List (Sum ι ι)) (i : ι) (f : (ι → ℕ) → GaussianInt) :=
  (CoordinateEnumeration.enumerate (width axis retained) fields (fun _ => 0)).flatMap fun coords =>
    cstream A w ((List.range (localLength axis retained i)).map fun j =>
      pullback axis retained f (Function.update (unpack coords) i (coords (.inl i),j)))

theorem suffix_archive (A w : ℕ) (axis : ι → Axis) (retained : Finset ι)
    (fields : List (Sum ι ι)) (i : ι) (f : (ι → ℕ) → GaussianInt) :
    CoordinateFieldLayout.stream (width axis retained) (fields++[Sum.inr i]) (fun _ => 0)
      (fun coords => csyms A w (pullback axis retained f (unpack coords))) =
      archive A w axis retained fields i f := by
  simp only [CoordinateFieldLayout.stream,CoordinateEnumeration.enumerate_append,
    List.flatMap_assoc,archive]
  apply List.flatMap_congr
  intro coords _
  have hup (j : ℕ) : unpack (Function.update coords (.inr i) j) =
      Function.update (unpack coords) i (coords (.inl i),j) := by
    funext x
    by_cases hx : x = i
    · subst x; simp [unpack]
    · simp [unpack,hx]
  simp only [CoordinateEnumeration.enumerate,List.flatMap_cons,List.flatMap_nil,
    List.append_nil,List.flatMap_assoc,List.flatMap_map,width,hup,cstream]

variable {T Q A : ℕ} {J U : Type} {body : J → Pr J T Q A U}

/-- The existing physical field permutation produces the actual local-field
archive, with its endpoint and space trace attached to that execution. -/
theorem expose_exec (r : Fin 16 → Fin T) (hr : Function.Injective r)
    (axis : ι → Axis) (retained : Finset ι) (left : List ι) (i : ι) (right : List ι)
    (hn : (left++i::right).Nodup) (w k : ℕ) (hw : 0 < w)
    (hfit : localLength axis retained i ≤ 2^k) (f : (ι → ℕ) → GaussianInt)
    (zero : Fin (A+4)) (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hh : FieldOrderRun.Headers r k
      ((moveBefore left i right).map (width axis retained)).prod
      ((moveMiddle right).map (width axis retained)).prod (localLength axis retained i) w S)
    (hf : ∀ j ∈ FieldOrderRun.scratch, S.R (r j) = [])
    (hsrc : S.R (r 11) = RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A w)++tail) :
    let V := ((moveBefore left i right).map (width axis retained)).prod*
      (((moveMiddle right).map (width axis retained)).prod*(2^k*w))
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(64*V+3)+384*V+2 ∧
      Exec body (FieldOrderRun.backward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (archive A w axis retained (moveBefore left i right++moveMiddle right) i f++tail))}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+1000*V)
        depth (FieldOrderRun.backward r zero) (mk v S) n
        (mk vf {S with R := (Function.update S.R (r 11)
          (archive A w axis retained (moveBefore left i right++moveMiddle right) i f++tail))})) := by
  have hex := HaloMixedOrderRun.toSuffix_exec (body := body) r hr axis retained left i right hn
    w k hw hfit f zero tail v S hh hf hsrc
  have harchive : HaloCoordinateAxis.source A w axis retained (haloBefore left) (haloMiddle left right) i f =
      archive A w axis retained (moveBefore left i right++moveMiddle right) i f := by
    rw [suffix_stream]
    simpa only [List.append_assoc] using
      suffix_archive A w axis retained (moveBefore left i right++moveMiddle right) i f
  simpa only [harchive,HaloMixedOrderRun.moveVolume] using hex

end IntegerMultBounds.MathlibTM2.Routing.RetainedFieldRun
