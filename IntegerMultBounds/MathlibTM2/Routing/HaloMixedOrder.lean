module

public import IntegerMultBounds.MathlibTM2.Routing.HaloCoordinateAxis
public import IntegerMultBounds.MathlibTM2.Routing.CoordinateFieldRun

/-! The two views used by a full mixed-order halo step. The selected local
field moves to the suffix, the halo pass runs, then the enlarged field returns. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloMixedOrder
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Routing
  RetainedHaloTensor RetainedTensorEnumeration
open IntegerMultBounds.MathlibTM2.Fast
variable {ι : Type} [DecidableEq ι]

def moveBefore (left : List ι) (i : ι) (right : List ι) : List (Sum ι ι) :=
  (left++i::right).map Sum.inl ++ left.map Sum.inr

def moveMiddle (right : List ι) : List (Sum ι ι) := right.map Sum.inr

def haloBefore (left : List ι) : List (Sum ι ι) := left.map Sum.inl

def haloMiddle (left right : List ι) : List (Sum ι ι) :=
  right.map Sum.inl ++ left.map Sum.inr ++ right.map Sum.inr

theorem mixed_stream (A w : ℕ) (axis : ι → Axis) (retained : Finset ι)
    (left : List ι) (i : ι) (right : List ι) (f : (ι → ℕ) → GaussianInt) :
    RetainedTensorEnumeration.stream axis retained (left++i::right) f (csyms A w) =
      CoordinateFieldLayout.stream (width axis retained)
        (moveBefore left i right++Sum.inr i::(moveMiddle right++[])) (fun _ => 0)
        (fun coords => csyms A w (pullback axis retained f (unpack coords))) := by
  rw [stream_field_order]
  simp only [order,moveBefore,moveMiddle,List.map_append,List.map_cons,List.append_nil,List.append_assoc]

theorem suffix_stream (A w : ℕ) (axis : ι → Axis) (retained : Finset ι)
    (left : List ι) (i : ι) (right : List ι) (f : (ι → ℕ) → GaussianInt) :
    HaloCoordinateAxis.source A w axis retained (haloBefore left) (haloMiddle left right) i f =
      CoordinateFieldLayout.stream (width axis retained)
        (moveBefore left i right++moveMiddle right++Sum.inr i::[]) (fun _ => 0)
        (fun coords => csyms A w (pullback axis retained f (unpack coords))) := by
  simp only [HaloCoordinateAxis.source,haloBefore,haloMiddle,moveBefore,moveMiddle,
    List.map_append,List.map_cons,List.append_assoc,List.cons_append]

omit [DecidableEq ι] in
theorem fields_fresh (left : List ι) (i : ι) (right : List ι) (hn : (left++i::right).Nodup) :
    Sum.inr i ∉ moveMiddle right ∧ Sum.inl i ∉ haloMiddle left right ∧
      Sum.inr i ∉ haloBefore left ∧ Sum.inr i ∉ haloMiddle left right := by
  have hs := List.nodup_append'.mp hn
  have hir : i ∉ right := (List.nodup_cons.mp hs.2.1).1
  have hil : i ∉ left := fun hi => List.disjoint_left.mp hs.2.2 hi (by simp)
  simp [moveMiddle,haloMiddle,haloBefore,hir,hil]

theorem width_pos (axis : ι → Axis) (retained : Finset ι) (j : Sum ι ι) : 0 < width axis retained j := by
  cases j with
  | inl j => exact (axis j).N_pos
  | inr j =>
    have h := (axis j).L_pos
    simp only [width,localLength]
    split_ifs <;> omega

theorem product_pos (axis : ι → Axis) (retained : Finset ι) (fields : List (Sum ι ι)) :
    0 < (fields.map (width axis retained)).prod := by
  apply List.prod_pos
  intro n hn
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hn
  exact width_pos axis retained j

end IntegerMultBounds.MathlibTM2.Routing.HaloMixedOrder
