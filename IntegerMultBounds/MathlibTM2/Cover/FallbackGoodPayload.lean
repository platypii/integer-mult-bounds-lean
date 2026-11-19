module

public import IntegerMultBounds.Machine.ArbitraryWidthSliceTranspose
public import IntegerMultBounds.MathlibTM2.Cover.Weighted

/-! Views of a two-field payload for a head pass or a family of tail passes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine FlatCoordinateLayout
variable {a b M W : ℕ} [NeZero M] {α : Type*}

theorem payloadVolume (M a b W : ℕ) : M^a*(M^b*W) = M^(a+b)*W := by
  rw [pow_add,Nat.mul_assoc]

/-- The tail address and trailing symbol together are the head pass's record index. -/
theorem headPayload_index (x : Fin a → ZMod M) (y : Fin b → ZMod M) (j : Fin W) :
    (index x (index y j)).cast (payloadVolume M a b W) = index (Fin.append x y) j := by
  apply Fin.ext
  simp only [Fin.val_cast,index_val]
  change _ = (rank (Fin.addCases x y)).val*W+j.val
  rw [ArbitraryWidthSliceTranspose.rank_append]
  ring

/-- A head address selects a contiguous tail payload in the combined array. -/
noncomputable def tailPayloadIndex (x : Fin a → ZMod M) (t : Fin (M^b*W)) : Fin (M^(a+b)*W) :=
  (finProdFinEquiv (rank x,t)).cast (payloadVolume M a b W)

theorem tailPayload_index (x : Fin a → ZMod M) (y : Fin b → ZMod M) (j : Fin W) :
    tailPayloadIndex x (index y j) = index (Fin.append x y) j := headPayload_index x y j

theorem headPayload_effect (f : (Fin a → ZMod M) → Fin a → ZMod M)
    (word out : Fin (M^(a+b)*W) → α)
    (run : ∀ x (t : Fin (M^b*W)), out ((index (f x) t).cast (payloadVolume M a b W)) =
      word ((index x t).cast (payloadVolume M a b W))) (x : Fin a → ZMod M) (y : Fin b → ZMod M) (j : Fin W) :
    out (index (Fin.append (f x) y) j) = word (index (Fin.append x y) j) := by
  simpa only [headPayload_index] using run x (index y j)

theorem tailPayload_effect (f : (Fin b → ZMod M) → Fin b → ZMod M)
    (word out : Fin (M^(a+b)*W) → α)
    (run : ∀ (x : Fin a → ZMod M) y (j : Fin W),
      out (tailPayloadIndex x (index (f y) j)) = word (tailPayloadIndex x (index y j)))
    (x : Fin a → ZMod M) (y : Fin b → ZMod M) (j : Fin W) :
    out (index (Fin.append x (f y)) j) = word (index (Fin.append x y) j) := by
  simpa only [tailPayload_index] using run x y j

/-- Put a child's head and tail on either side of the two inactive slices.
The tail field has the same total width as the head, in reversed slice order. -/
def childFields {r g : ℕ} {R : Type*} (headGap tailGap : Fin g → R)
    (s : (Fin r → R) × (Fin r → R)) : (Fin (r+g) → R) × (Fin (r+g) → R) :=
  (Fin.append s.1 headGap,fun i => Fin.append tailGap s.2 (i.cast (Nat.add_comm r g)))

theorem childFields_apply {r g : ℕ} {R : Type*} [CommRing R] (w w' : Fin (r+g) → R)
    (headGap tailGap : Fin g → R) (s : (Fin r → R) × (Fin r → R)) :
    Weighted.child r w w' (childFields headGap tailGap s) =
      childFields headGap tailGap (Weighted.child r (fun i => w (i.castAdd g)) (fun i => w' (i.castAdd g)) s) := by
  have tail (y : Fin r → R) (i : Fin (r+g)) :
      Fin.append tailGap y (i.rev.cast (Nat.add_comm r g)) =
        Fin.append (y ∘ Fin.rev) (tailGap ∘ Fin.rev) i := by
    simpa only [Function.comp_def,Fin.rev_rev] using
      (Fin.append_rev (y ∘ Fin.rev) (tailGap ∘ Fin.rev) i.rev).symm
  apply Prod.ext
  · funext i
    induction i using Fin.addCases with
    | left i => simp only [Weighted.child,childFields,Fin.val_castAdd,i.isLt,ite_true,tail,Fin.append_left,Function.comp_apply]
    | right i =>
      have hi : ¬ (i.natAdd r).val < r := by change ¬ r+i.val < r; omega
      simp only [Weighted.child,childFields,hi,ite_false,Fin.append_right]
  · funext i
    obtain ⟨i,rfl⟩ := Fin.rev_surjective i
    induction i using Fin.addCases with
    | left i =>
      simp only [Weighted.child,childFields,Fin.rev_rev,Fin.val_castAdd,i.isLt,ite_true,tail,Fin.append_left,Function.comp_apply]
    | right i =>
      have hi : ¬ (i.natAdd r).val < r := by change ¬ r+i.val < r; omega
      simp only [Weighted.child,childFields,Fin.rev_rev,hi,ite_false,tail,Fin.append_right,Function.comp_apply]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
