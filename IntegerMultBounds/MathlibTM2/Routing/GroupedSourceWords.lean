module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceGroup

/-! Word repetition agrees with repeated source-profile entries. These identities
keep the group generator's executable block format separate from its specification. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
variable {A : ℕ}

theorem affineProfileFrames_append (L : ℕ) (xs ys : List (Bool × ℕ)) :
    affineProfileFrames (A := A) L (xs ++ ys) = affineProfileFrames L xs ++ affineProfileFrames L ys := by
  induction xs with
  | nil => simp [affineProfileFrames]
  | cons x xs ih =>
    obtain ⟨b, q⟩ := x
    simp [affineProfileFrames, ih, List.append_assoc]

theorem wordCopies_affineProfileFrame (L : ℕ) (x : Bool × ℕ) (n : ℕ) :
    wordCopies (affineProfileFrames (A := A) L [x]) n = affineProfileFrames L (List.replicate n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wordCopies, ih, List.replicate_succ', affineProfileFrames_append]

end IntegerMultBounds.MathlibTM2.Routing
