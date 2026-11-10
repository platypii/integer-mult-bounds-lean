module

public import IntegerMultBounds.MathlibTM2.Routing.RetainedFieldRun

/-! The actual prefix/coarse/spectator stream supplies same-owner batches. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RetainedFieldBatch
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  RetainedHaloTensor RetainedTensorEnumeration CoordinateFieldLayout
variable {ι : Type} [DecidableEq ι]

def replicas (axis : ι → Axis) (retained : Finset ι)
    (before middle : List (Sum ι ι)) (a : ℕ) : List (ι → ℕ × ℕ) :=
  (List.range ((middle.map (width axis retained)).prod)).map
    (HaloCoordinateLayout.base axis retained before middle a)

@[simp] theorem replicas_length (axis : ι → Axis) (retained : Finset ι)
    (before middle : List (Sum ι ι)) (a : ℕ) :
    (replicas axis retained before middle a).length =
      (middle.map (width axis retained)).prod := by simp [replicas]

theorem replicas_valid (axis : ι → Axis) (retained : Finset ι)
    (before middle : List (Sum ι ι)) (a : ℕ) :
    ∀ coords ∈ replicas axis retained before middle a, Valid axis retained coords := by
  intro coords hc
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hc
  have hzero : ∀ j, (0 : ℕ) < width axis retained j := HaloMixedOrder.width_pos axis retained
  have hbefore := coordsAt_bounded (width axis retained) before (fun _ => 0) hzero a
  have hmiddle := coordsAt_bounded (width axis retained) middle _ hbefore b
  intro i
  exact ⟨hmiddle (.inl i),hmiddle (.inr i)⟩

def batch (A w : ℕ) (axis : ι → Axis) (retained : Finset ι)
    (before middle : List (Sum ι ι)) (i : ι) (a k : ℕ) (f : (ι → ℕ) → GaussianInt) :=
  (replicas axis retained before middle a).flatMap fun coords =>
    cstream A w ((List.range (localLength axis retained i)).map fun j =>
      pullback axis retained f (Function.update coords i (k,j)))

/-- The batch order is the order produced by the physical suffix permutation.
Only a prefix and a coarse owner vary between batches; the controller is shared
across the complete computed spectator list. -/
theorem source_batches (A w : ℕ) (axis : ι → Axis) (retained : Finset ι)
    (before middle : List (Sum ι ι)) (i : ι) (hi : Sum.inl i ∉ middle)
    (f : (ι → ℕ) → GaussianInt) :
    HaloCoordinateAxis.source A w axis retained before middle i f =
      (List.range ((before.map (width axis retained)).prod)).flatMap fun a =>
        (List.range (axis i).N).flatMap fun k => batch A w axis retained before middle i a k f := by
  unfold HaloCoordinateAxis.source CoordinateFieldLayout.stream
  rw [CoordinateEnumeration.enumerate_append,List.flatMap_assoc]
  rw [flatMap_range_getD (CoordinateEnumeration.enumerate (width axis retained) before (fun _ => 0))
    (fun _ => 0)]
  simp only [CoordinateEnumeration.enumerate_length]
  apply List.flatMap_congr
  intro a _
  simp only [CoordinateEnumeration.enumerate,width,List.flatMap_assoc]
  apply List.flatMap_congr
  intro k _
  rw [CoordinateEnumeration.enumerate_append,List.flatMap_assoc]
  rw [CoordinateFieldLayout.enumerate_update_other (width axis retained) middle (.inl i) hi]
  simp only [List.flatMap_map]
  rw [flatMap_range_getD (CoordinateEnumeration.enumerate (width axis retained) middle _)
    (coordsAt (width axis retained) before (fun _ => 0) a)]
  simp only [CoordinateEnumeration.enumerate_length,batch,replicas,List.flatMap_map]
  apply List.flatMap_congr
  intro b _
  simp only [CoordinateEnumeration.enumerate,width,List.flatMap_assoc,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,HaloCoordinateLayout.unpack_update_pair,
    HaloCoordinateLayout.base,coordsAt,cstream,List.flatMap_map]

/-- Apply the batch decomposition to the endpoint of `expose_exec`. -/
theorem exposed_batches (A w : ℕ) (axis : ι → Axis) (retained : Finset ι)
    (left : List ι) (i : ι) (right : List ι) (hn : (left++i::right).Nodup)
    (f : (ι → ℕ) → GaussianInt) :
    RetainedFieldRun.archive A w axis retained
      (HaloMixedOrder.moveBefore left i right++HaloMixedOrder.moveMiddle right) i f =
      (List.range (((HaloMixedOrder.haloBefore left).map (width axis retained)).prod)).flatMap fun a =>
        (List.range (axis i).N).flatMap fun k =>
          batch A w axis retained (HaloMixedOrder.haloBefore left)
            (HaloMixedOrder.haloMiddle left right) i a k f := by
  have hsource : HaloCoordinateAxis.source A w axis retained (HaloMixedOrder.haloBefore left)
      (HaloMixedOrder.haloMiddle left right) i f =
      RetainedFieldRun.archive A w axis retained
        (HaloMixedOrder.moveBefore left i right++HaloMixedOrder.moveMiddle right) i f := by
    rw [HaloMixedOrder.suffix_stream]
    simpa only [List.append_assoc] using RetainedFieldRun.suffix_archive A w axis retained
      (HaloMixedOrder.moveBefore left i right++HaloMixedOrder.moveMiddle right) i f
  rw [←hsource]
  exact source_batches A w axis retained _ _ i (HaloMixedOrder.fields_fresh left i right hn).2.1 f

end IntegerMultBounds.MathlibTM2.Routing.RetainedFieldBatch
