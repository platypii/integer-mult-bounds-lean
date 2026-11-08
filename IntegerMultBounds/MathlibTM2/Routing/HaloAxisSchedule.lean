module

public import IntegerMultBounds.MathlibTM2.Routing.HaloMetadataAxis

/-! Runtime metadata for a sequence of actual halo-axis calls. The retained set
advances structurally; packets use the exact current mixed tensor dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloAxisSchedule
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Routing
  HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisTensorInvariant
  HaloMixedOrder HaloMixedOrderRun
variable {ι : Type} [DecidableEq ι]

structure Stage (ι : Type) where
  params : Parameters
  left : List ι
  i : ι
  right : List ι

def after : Finset ι → List (Stage ι) → Finset ι
  | retained, [] => retained
  | retained, s::stages => after (insert s.i retained) stages

def xs (axis : ι → Axis) (retained : Finset ι) (s : Stage ι) := (haloBefore s.left).map (width axis retained)
def ys (axis : ι → Axis) (retained : Finset ι) (s : Stage ι) := (moveBefore s.left s.i s.right).map (width axis retained)
def zs (axis : ι → Axis) (retained : Finset ι) (s : Stage ι) := (moveMiddle s.right).map (width axis retained)

structure Ready (axis : ι → Axis) (retained : Finset ι) (s : Stage ι) : Prop where
  fresh : s.i ∉ retained
  axis_eq : axis s.i = axisOf s.params
  spectator : ((haloMiddle s.left s.right).map (width axis retained)).prod = s.params.B
  masters_fit : ∀ e ∈ HaloAxisMasterSetup.entries s.params, e.2 < 2^s.params.V
  factors_fit : ∀ x ∈ xs axis retained s++ys axis retained s++zs axis retained s, x < 2^s.params.V
  count_fit : ∀ ds ∈ [xs axis retained s,ys axis retained s,zs axis retained s], ds.length < 2^s.params.V

def stagePacket (A : ℕ) (axis : ι → Axis) (retained : Finset ι) (s : Stage ι) :=
  HaloMetadataAxis.packet A s.params (xs axis retained s) (ys axis retained s) (zs axis retained s)

def metadata (A : ℕ) (axis : ι → Axis) : Finset ι → List (Stage ι) → List (Fin (A+4))
  | _, [] => []
  | retained, s::stages => stagePacket A axis retained s++metadata A axis (insert s.i retained) stages

def time (axis : ι → Axis) (retained : Finset ι) (s : Stage ι) :=
  HaloMetadataAxis.cost s.params (xs axis retained s) (ys axis retained s) (zs axis retained s)
    (moveVolume axis retained s.left s.i s.right s.params.k s.params.w)
    (moveVolume axis (insert s.i retained) s.left s.i s.right s.params.r s.params.w)

def reserve (axis : ι → Axis) (retained : Finset ι) (s : Stage ι) :=
  HaloMetadataAxis.reserve s.params (xs axis retained s) (ys axis retained s) (zs axis retained s)
    (moveVolume axis retained s.left s.i s.right s.params.k s.params.w)
    (moveVolume axis (insert s.i retained) s.left s.i s.right s.params.r s.params.w)

theorem after_append (retained : Finset ι) (xs ys : List (Stage ι)) :
    after retained (xs++ys) = after (after retained xs) ys := by
  induction xs generalizing retained with
  | nil => rfl
  | cons s xs ih => exact ih _

theorem after_snoc (retained : Finset ι) (stages : List (Stage ι)) (s : Stage ι) :
    after retained (stages++[s]) = insert s.i (after retained stages) := by rw [after_append]; rfl

theorem metadata_append (A : ℕ) (axis : ι → Axis) (retained : Finset ι) (xs ys : List (Stage ι)) :
    metadata A axis retained (xs++ys) = metadata A axis retained xs++metadata A axis (after retained xs) ys := by
  induction xs generalizing retained with
  | nil => simp [metadata,after]
  | cons s xs ih => simp only [List.cons_append,metadata,after,ih,List.append_assoc]

theorem after_eq_union (retained : Finset ι) (stages : List (Stage ι)) :
    after retained stages = retained ∪ (stages.map Stage.i).toFinset := by
  induction stages generalizing retained with
  | nil => simp [after]
  | cons s stages ih =>
    rw [after,ih]
    ext i
    simp only [Finset.mem_union,Finset.mem_insert,List.map_cons,List.toFinset_cons]
    tauto

theorem after_all [Fintype ι] (stages : List (Stage ι)) (hall : ∀ i, i ∈ stages.map Stage.i) :
    after ∅ stages = Finset.univ := by
  rw [after_eq_union]
  ext i
  simp [hall i]

end IntegerMultBounds.MathlibTM2.Routing.HaloAxisSchedule
