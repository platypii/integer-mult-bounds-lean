module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodPayload

/-! The rank child reads both active fields in place, with the inactive digits
packed into the middle field of the recursive interchange descriptor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine FlatCoordinateLayout
variable {r g M W : ℕ} [NeZero M]

def goodChildDescriptor (M r g W : ℕ) : RecursiveInterchangeLayout.Descriptor :=
  ⟨1,1,1,r,M^(g+g),W⟩

theorem goodChildVolume (M r g W : ℕ) :
    RecursiveInterchangeLayout.volume M (goodChildDescriptor M r g W) = M^((r+g)+(r+g))*W := by
  simp only [RecursiveInterchangeLayout.volume,goodChildDescriptor,one_mul,pow_add]
  ring

private theorem rank_join {a b : ℕ} (x : Fin a → ZMod M) (y : Fin b → ZMod M) :
    (rank (Fin.append x y)).val = (rank x).val*M^b+(rank y).val :=
  ArbitraryWidthSliceTranspose.rank_append x y

private theorem rank_cast {a b : ℕ} (h : a = b) (x : Fin b → ZMod M) :
    (rank (fun i : Fin a => x (i.cast h))).val = (rank x).val := by subst b; rfl

theorem goodChildIndex (hg tg : Fin g → ZMod M) (s : (Fin r → ZMod M) × (Fin r → ZMod M)) (j : Fin W) :
    let t := childFields hg tg s
    (index (Fin.append t.1 t.2) j).val =
      RecursiveInterchangeLayout.index M (goodChildDescriptor M r g W) 0 0 0
        (rank s.1).val (rank (Fin.append hg tg)).val (rank s.2).val j.val := by
  dsimp only [childFields]
  rw [index_val,rank_join,rank_join,rank_cast,rank_join,rank_join]
  simp only [RecursiveInterchangeLayout.index,goodChildDescriptor,Nat.zero_mul,Nat.zero_add,pow_add]
  ring

theorem childFields_surjective {R : Type*} (x y : Fin (r+g) → R) :
    ∃ hg tg s, childFields hg tg s = (x,y) := by
  let z := fun i : Fin (g+r) => y (i.cast (Nat.add_comm g r))
  refine ⟨fun i => x (i.natAdd r),fun i => z (i.castAdd r),
    (fun i => x (i.castAdd g),fun i => z (i.natAdd g)),?_⟩
  have split {a b : ℕ} (f : Fin (a+b) → R) :
      Fin.append (fun i => f (i.castAdd b)) (fun i => f (i.natAdd a)) = f := by
    funext i
    induction i using Fin.addCases <;> simp
  apply Prod.ext
  · exact split x
  · funext i
    dsimp only [childFields]
    rw [split z]
    rfl

/-- A recursive action on the two rank fields induces the parent action at every
serialized address, including both spectator fields and every trailing symbol. -/
theorem goodChild_effect {α : Type*} (w w' : Fin (r+g) → ZMod M)
    (word out : Fin (M^((r+g)+(r+g))*W) → α)
    (run : ∀ (hg tg : Fin g → ZMod M) (s : (Fin r → ZMod M) × (Fin r → ZMod M)) (j : Fin W),
      let encode := fun u => let t := childFields hg tg u; index (Fin.append t.1 t.2) j
      out (encode (Weighted.child r (fun i => w (i.castAdd g)) (fun i => w' (i.castAdd g)) s)) =
        word (encode s))
    (x y : Fin (r+g) → ZMod M) (j : Fin W) :
    let t := Weighted.child r w w' (x,y)
    out (index (Fin.append t.1 t.2) j) = word (index (Fin.append x y) j) := by
  obtain ⟨hg,tg,s,eq⟩ := childFields_surjective x y
  have h := run hg tg s j
  dsimp only at h
  rw [← childFields_apply w w' hg tg s,eq] at h
  exact h

end IntegerMultBounds.MathlibTM2.Cover.Fallback
