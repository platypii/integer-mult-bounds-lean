module

public import IntegerMultBounds.MathlibTM2.Routing.RetainedHaloTensor
public import IntegerMultBounds.MathlibTM2.Routing.CoordinateEnumeration
public import IntegerMultBounds.MathlibTM2.Routing.CoordinateFieldLayout

/-! The manuscript's mixed tensor order: all coarse fields precede all local
fields. Previously retained local fields have their actual enlarged widths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.RetainedTensorEnumeration
open RetainedHaloTensor
variable {ι : Type} [DecidableEq ι]

def width (axis : ι → Axis) (retained : Finset ι) : Sum ι ι → ℕ
  | .inl i => (axis i).N
  | .inr i => localLength axis retained i

def order (axes : List ι) : List (Sum ι ι) := axes.map Sum.inl ++ axes.map Sum.inr

def pack (coords : ι → ℕ × ℕ) : Sum ι ι → ℕ := Sum.elim (fun i => (coords i).1) (fun i => (coords i).2)
def unpack (coords : Sum ι ι → ℕ) : ι → ℕ × ℕ := fun i => (coords (.inl i),coords (.inr i))

def enumerate (axis : ι → Axis) (retained : Finset ι) (axes : List ι) : List (ι → ℕ × ℕ) :=
  (CoordinateEnumeration.enumerate (width axis retained) (order axes) (fun _ => 0)).map unpack

omit [DecidableEq ι] in
theorem pack_unpack (coords : Sum ι ι → ℕ) : pack (unpack coords) = coords := by
  funext i; cases i <;> rfl

omit [DecidableEq ι] in
theorem unpack_pack (coords : ι → ℕ × ℕ) : unpack (pack coords) = coords := by
  funext i; exact Prod.eta _

omit [DecidableEq ι] in
theorem order_nodup (axes : List ι) (hn : axes.Nodup) : (order axes).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨hn.map Sum.inl_injective,hn.map Sum.inr_injective,?_⟩
  apply List.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,_,he⟩ := List.mem_map.mp hy
  cases he

theorem enumerate_length (axis : ι → Axis) (retained : Finset ι) (axes : List ι) :
    (enumerate axis retained axes).length =
      (axes.map fun i => (axis i).N).prod*(axes.map fun i => localLength axis retained i).prod := by
  simp [enumerate,CoordinateEnumeration.enumerate_length,order,width,List.map_map,Function.comp_def]

theorem mem_enumerate_all (axis : ι → Axis) (retained : Finset ι) (axes : List ι)
    (hn : axes.Nodup) (hall : ∀ i, i ∈ axes) (coords : ι → ℕ × ℕ) :
    coords ∈ enumerate axis retained axes ↔ Valid axis retained coords := by
  have hfields : ∀ j, j ∈ order axes := by
    intro j; cases j with
    | inl i => simp [order,hall i]
    | inr i => simp [order,hall i]
  have hmem := CoordinateEnumeration.mem_enumerate (width axis retained) (order axes) (order_nodup axes hn)
    (fun _ => 0) (pack coords)
  constructor
  · intro hc
    obtain ⟨fields,hf,he⟩ := List.mem_map.mp hc
    have he' : fields = pack coords := by rw [←he,pack_unpack]
    subst fields
    have hv := (hmem.mp hf).1
    intro i
    exact ⟨hv (.inl i) (hfields _),hv (.inr i) (hfields _)⟩
  · intro hv
    apply List.mem_map.mpr
    refine ⟨pack coords,hmem.mpr ⟨?_,?_⟩,unpack_pack coords⟩
    · intro j _; cases j with
      | inl i => exact (hv i).1
      | inr i => exact (hv i).2
    · intro j hj; exact False.elim (hj (hfields j))

theorem enumerate_nodup (axis : ι → Axis) (retained : Finset ι) (axes : List ι) (hn : axes.Nodup) :
    (enumerate axis retained axes).Nodup := by
  apply List.Nodup.map _ (CoordinateEnumeration.enumerate_nodup _ _ (order_nodup axes hn) _)
  intro x y he
  rw [←pack_unpack x,←pack_unpack y,he]

theorem enumerate_length_eq_volume [Fintype ι] (axis : ι → Axis) (retained : Finset ι) (axes : List ι)
    (hn : axes.Nodup) (hall : ∀ i, i ∈ axes) :
    (enumerate axis retained axes).length = volume axis retained := by
  have hu : axes.toFinset = Finset.univ := by ext i; simp [hall i]
  rw [enumerate_length,←List.prod_toFinset (fun i => (axis i).N) hn,
    ←List.prod_toFinset (fun i => localLength axis retained i) hn,hu,←Finset.prod_mul_distrib]
  rfl

def stream {E Γ : Type} (axis : ι → Axis) (retained : Finset ι) (axes : List ι)
    (f : (ι → ℕ) → E) (encode : E → List Γ) : List Γ :=
  (enumerate axis retained axes).flatMap fun coords => encode (pullback axis retained f coords)

theorem stream_field_order {E Γ : Type} (axis : ι → Axis) (retained : Finset ι) (axes : List ι)
    (f : (ι → ℕ) → E) (encode : E → List Γ) :
    stream axis retained axes f encode = CoordinateFieldLayout.stream (width axis retained) (order axes)
      (fun _ => 0) (fun coords => encode (pullback axis retained f (unpack coords))) := by
  simp only [stream,enumerate,List.flatMap_map,CoordinateFieldLayout.stream]

theorem stream_length {E Γ : Type} [Fintype ι] (axis : ι → Axis) (retained : Finset ι)
    (axes : List ι) (hn : axes.Nodup) (hall : ∀ i, i ∈ axes)
    (f : (ι → ℕ) → E) (encode : E → List Γ) (R : ℕ) (hencode : ∀ x, (encode x).length = R) :
    (stream axis retained axes f encode).length = volume axis retained*R := by
  rw [stream,HaloRecordLayout.length_flatMap _ R _ (fun coords _ => hencode _),
    enumerate_length_eq_volume axis retained axes hn hall]

end IntegerMultBounds.MathlibTM2.Routing.RetainedTensorEnumeration
