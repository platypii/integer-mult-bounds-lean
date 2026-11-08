module

public import IntegerMultBounds.MathlibTM2.Routing.RetainedTensorEnumeration
public import IntegerMultBounds.MathlibTM2.Routing.HaloAxisTensorLayout

/-! Identify the enumerated coarse/spectator/local stream with the actual halo
pass input. The prefix/spectator coordinate base is computed, not supplied. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloCoordinateLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Routing
  CoordinateEnumeration CoordinateFieldLayout RetainedHaloTensor RetainedTensorEnumeration HaloPassContext
open IntegerMultBounds.MathlibTM2.Fast
variable {ι : Type} [DecidableEq ι]

theorem coordsAt_update_other {κ : Type} [DecidableEq κ] (width : κ → ℕ) (fields : List κ)
    (i : κ) (hi : i ∉ fields) (coords : κ → ℕ) (t n : ℕ) :
    coordsAt width fields (Function.update coords i t) n = Function.update (coordsAt width fields coords n) i t := by
  simp only [coordsAt,enumerate_update_other width fields i hi,List.getElem?_map]
  cases (enumerate width fields coords)[n]? <;> rfl

theorem unpack_update_pair (coords : Sum ι ι → ℕ) (i : ι) (k t : ℕ) :
    unpack (Function.update (Function.update coords (.inl i) k) (.inr i) t) =
      Function.update (unpack coords) i (k,t) := by
  funext j
  by_cases hji : j = i
  · subst j; simp [unpack]
  · simp [unpack,hji]

def base (axis : ι → Axis) (retained : Finset ι) (before middle : List (Sum ι ι)) (a b : ℕ) : ι → ℕ × ℕ :=
  unpack (coordsAt (width axis retained) middle (coordsAt (width axis retained) before (fun _ => 0) a) b)

theorem stream_layout (A w : ℕ) (p : Parameters) (hw : p.w = w)
    (axis : ι → Axis) (retained : Finset ι) (i : ι) (before middle : List (Sum ι ι))
    (hi : Sum.inl i ∉ middle) (N B M : ℕ)
    (hN : (axis i).N = N) (hB : (middle.map (width axis retained)).prod = B)
    (hM : localLength axis retained i = M) (f : (ι → ℕ) → GaussianInt) :
    CoordinateFieldLayout.stream (width axis retained) (before++Sum.inl i::(middle++[Sum.inr i]))
      (fun _ => 0) (fun coords => csyms A w (pullback axis retained f (unpack coords))) =
      (HaloAxisTensorLayout.layout (before.map (width axis retained)).prod N B M axis retained i
        (base axis retained before middle) f).flatMap (HaloPassContext.input A p) := by
  unfold CoordinateFieldLayout.stream
  rw [enumerate_append,List.flatMap_assoc]
  rw [flatMap_range_getD (enumerate (width axis retained) before (fun _ => 0)) (fun _ => 0)]
  simp only [CoordinateEnumeration.enumerate_length]
  simp only [HaloAxisTensorLayout.layout,TensorFiberLayout.tabulate,HaloPassContext.input,
    PaddedFieldLayout.sourceRows,List.flatten_eq_flatMap,List.flatMap_map,List.flatMap_assoc,id_eq,hw]
  apply List.flatMap_congr
  intro a _
  simp only [CoordinateEnumeration.enumerate,RetainedTensorEnumeration.width,hN,List.flatMap_assoc]
  apply List.flatMap_congr
  intro k _
  rw [enumerate_append,List.flatMap_assoc]
  rw [flatMap_range_getD (enumerate (width axis retained) middle _)
    (Function.update (coordsAt (width axis retained) before (fun _ => 0) a) (.inl i) k)]
  simp only [CoordinateEnumeration.enumerate_length,hB]
  apply List.flatMap_congr
  intro b _
  simp only [CoordinateEnumeration.enumerate,RetainedTensorEnumeration.width,hM,List.flatMap_assoc,List.flatMap_singleton]
  apply List.flatMap_congr
  intro t _
  change csyms A w (pullback axis retained f (unpack (Function.update
    (coordsAt (width axis retained) middle
      (Function.update (coordsAt (width axis retained) before (fun _ => 0) a) (.inl i) k) b) (.inr i) t))) = _
  rw [coordsAt_update_other (width axis retained) middle (.inl i) hi,unpack_update_pair]
  rfl

theorem enumerate_width_congr {κ : Type} [DecidableEq κ] (v w : κ → ℕ) (fields : List κ)
    (h : ∀ j ∈ fields, v j = w j) (coords : κ → ℕ) :
    CoordinateEnumeration.enumerate v fields coords = CoordinateEnumeration.enumerate w fields coords := by
  induction fields generalizing coords with
  | nil => rfl
  | cons j fields ih =>
    simp only [CoordinateEnumeration.enumerate,h j (by simp)]
    apply List.flatMap_congr
    intro t _
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

theorem width_insert_other (axis : ι → Axis) (retained : Finset ι) (i : ι) (j : Sum ι ι)
    (hj : j ≠ Sum.inr i) : width axis (insert i retained) j = width axis retained j := by
  cases j with
  | inl j => rfl
  | inr j =>
    have hji : j ≠ i := fun he => hj (congrArg Sum.inr he)
    simp [width,localLength,hji]

theorem map_width_insert (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (fields : List (Sum ι ι)) (hi : Sum.inr i ∉ fields) :
    fields.map (width axis (insert i retained)) = fields.map (width axis retained) := by
  apply List.map_congr_left
  intro j hj
  exact width_insert_other axis retained i j (fun he => hi (he ▸ hj))

theorem coordsAt_insert (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (fields : List (Sum ι ι)) (hi : Sum.inr i ∉ fields) (coords : Sum ι ι → ℕ) (n : ℕ) :
    coordsAt (width axis (insert i retained)) fields coords n = coordsAt (width axis retained) fields coords n := by
  unfold coordsAt
  rw [enumerate_width_congr (width axis (insert i retained)) (width axis retained) fields
    (fun j hj => width_insert_other axis retained i j (fun he => hi (he ▸ hj)))]

theorem base_insert (axis : ι → Axis) (retained : Finset ι) (i : ι)
    (before middle : List (Sum ι ι)) (hb : Sum.inr i ∉ before) (hm : Sum.inr i ∉ middle) :
    base axis (insert i retained) before middle = base axis retained before middle := by
  funext a b
  simp only [base,coordsAt_insert axis retained i before hb,coordsAt_insert axis retained i middle hm]

end IntegerMultBounds.MathlibTM2.Routing.HaloCoordinateLayout
