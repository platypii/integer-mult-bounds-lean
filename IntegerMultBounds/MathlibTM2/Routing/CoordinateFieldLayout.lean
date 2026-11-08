module

public import IntegerMultBounds.MathlibTM2.Routing.CoordinateEnumeration
public import IntegerMultBounds.MathlibTM2.Routing.FieldOrderLayout

/-! Split a coordinate stream into before, spectator, selected field and a
fixed-width suffix record. Every fiber is derived from the actual enumeration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.CoordinateFieldLayout
open CoordinateEnumeration
variable {ι Γ E : Type} [DecidableEq ι]

theorem flatMap_range_getD (xs : List E) (fill : E) (f : E → List Γ) :
    xs.flatMap f = (List.range xs.length).flatMap (fun i => f ((xs[i]?).getD fill)) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.length_cons,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map,
      List.getElem?_cons_zero,Option.getD_some,List.getElem?_cons_succ]
    rw [ih]

theorem enumerate_update_other (width : ι → ℕ) (fields : List ι) (i : ι) (hi : i ∉ fields)
    (base : ι → ℕ) (t : ℕ) :
    enumerate width fields (Function.update base i t) =
      (enumerate width fields base).map (fun coords => Function.update coords i t) := by
  induction fields generalizing base with
  | nil => simp [enumerate]
  | cons j fields ih =>
    have hij : i ≠ j := fun he => hi (by simp [he])
    have hit : i ∉ fields := fun he => hi (List.mem_cons_of_mem j he)
    simp only [enumerate,List.map_flatMap]
    apply List.flatMap_congr
    intro u _
    rw [Function.update_comm hij,ih hit]

def stream (width : ι → ℕ) (fields : List ι) (base : ι → ℕ) (payload : (ι → ℕ) → List Γ) :=
  (enumerate width fields base).flatMap payload

def coordsAt (width : ι → ℕ) (fields : List ι) (base : ι → ℕ) (n : ℕ) :=
  ((enumerate width fields base)[n]?).getD base

abbrev Block (Γ : Type) (R : ℕ) := {xs : List Γ // xs.length = R}

def record (width : ι → ℕ) (suffix : List ι) (R : ℕ) (payload : (ι → ℕ) → List Γ)
    (hlen : ∀ coords, (payload coords).length = R) (coords : ι → ℕ) : Block Γ ((suffix.map width).prod*R) :=
  ⟨stream width suffix coords payload,by
    rw [stream,HaloRecordLayout.length_flatMap payload R _ (fun x _ => hlen x),enumerate_length]⟩

def data (width : ι → ℕ) (before middle suffix : List ι) (i : ι) (base : ι → ℕ)
    (R : ℕ) (payload : (ι → ℕ) → List Γ) (hlen : ∀ coords, (payload coords).length = R)
    (a b t : ℕ) : Block Γ ((suffix.map width).prod*R) :=
  record width suffix R payload hlen (Function.update (coordsAt width middle (coordsAt width before base a) b) i t)

theorem stream_grouped (width : ι → ℕ) (before middle suffix : List ι) (i : ι) (base : ι → ℕ)
    (R : ℕ) (payload : (ι → ℕ) → List Γ) (hlen : ∀ coords, (payload coords).length = R) :
    stream width (before++middle++i::suffix) base payload =
      FieldOrderLayout.stream Subtype.val (before.map width).prod (middle.map width).prod (width i)
        (data width before middle suffix i base R payload hlen) := by
  simp only [List.append_assoc]
  unfold stream
  rw [enumerate_append,List.flatMap_assoc]
  rw [flatMap_range_getD (enumerate width before base) base]
  simp only [enumerate_length]
  simp only [FieldOrderLayout.stream,FieldOrderLayout.fibers,FieldOrderLayout.rows,List.flatMap_map]
  apply List.flatMap_congr
  intro a _
  rw [enumerate_append,List.flatMap_assoc]
  rw [flatMap_range_getD (enumerate width middle _) (coordsAt width before base a)]
  simp only [enumerate_length]
  apply List.flatMap_congr
  intro b _
  simp only [enumerate,List.flatMap_assoc,data,record,stream,coordsAt]

theorem stream_swapped (width : ι → ℕ) (before middle suffix : List ι) (i : ι) (hi : i ∉ middle)
    (base : ι → ℕ) (R : ℕ) (payload : (ι → ℕ) → List Γ) (hlen : ∀ coords, (payload coords).length = R) :
    stream width (before++i::(middle++suffix)) base payload =
      FieldOrderLayout.stream Subtype.val (before.map width).prod (width i) (middle.map width).prod
        (fun a t b => data width before middle suffix i base R payload hlen a b t) := by
  unfold stream
  rw [enumerate_append,List.flatMap_assoc]
  rw [flatMap_range_getD (enumerate width before base) base]
  simp only [enumerate_length]
  simp only [FieldOrderLayout.stream,FieldOrderLayout.fibers,FieldOrderLayout.rows,List.flatMap_map]
  apply List.flatMap_congr
  intro a _
  simp only [enumerate,List.flatMap_assoc]
  apply List.flatMap_congr
  intro t _
  rw [enumerate_append,List.flatMap_assoc,enumerate_update_other width middle i hi,List.flatMap_map]
  rw [flatMap_range_getD (enumerate width middle _) (coordsAt width before base a)]
  simp only [enumerate_length,data,record,stream,coordsAt]

end IntegerMultBounds.MathlibTM2.Routing.CoordinateFieldLayout
