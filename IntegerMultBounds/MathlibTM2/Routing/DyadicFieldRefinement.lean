module

public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldMove

/-! A structural refinement path records the chronology of binary passes.
The inverse reads this proof relation backward, without inspecting payload data. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DyadicFieldRefinement
open DyadicFieldLayout DyadicFieldMove
variable {β : Type}

inductive Refines : {n k : ℕ} → List (List (Field β n)) → List (List (Field β k)) → Prop
  | refl {n : ℕ} (fs : List (List (Field β n))) : Refines fs fs
  | step {n k : ℕ} {fs : List (List (Field β n))} {gs : List (List (Field β (k+1)))} :
      Refines fs gs → Refines fs (refineFibers gs)

theorem Refines.trans {n k l : ℕ} {fs : List (List (Field β n))}
    {gs : List (List (Field β k))} {hs : List (List (Field β l))}
    (h : Refines fs gs) (h' : Refines gs hs) : Refines fs hs := by
  induction h' with
  | refl => exact h
  | step _ ih => exact .step (ih h)

theorem Refines.level_le {n k : ℕ} {fs : List (List (Field β n))} {gs : List (List (Field β k))}
    (h : Refines fs gs) : k ≤ n := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => omega

theorem Refines.eq_of_same {n : ℕ} {fs gs : List (List (Field β n))}
    (h : Refines fs gs) : fs = gs := by
  cases h with
  | refl => rfl
  | step h => have hh := h.level_le; omega

theorem Refines.complete {n : ℕ} (fs : List (List (Field β n))) : Refines (n := n) (k := 0) fs (finish (β := β) (k := n) fs) := by
  induction n with
  | zero => simpa only [finish_zero] using Refines.refl fs
  | succ n ih =>
    have h := (Refines.step (Refines.refl fs)).trans (ih (refineFibers fs))
    simpa only [finish_refine] using h

theorem Refines.row_length {n k : ℕ} {fs : List (List (Field β n))} {gs : List (List (Field β k))}
    (h : Refines fs gs) (B : ℕ) (hlen : ∀ rows ∈ fs, rows.length = B) :
    ∀ rows ∈ gs, rows.length = B := by
  induction h with
  | refl => exact hlen
  | step _ ih => exact refineFibers_row_length _ B (ih hlen)

theorem Refines.positive {n k : ℕ} {fs : List (List (Field β n))} {gs : List (List (Field β k))}
    (h : Refines fs gs) (hpos : 0 < fs.length) : 0 < gs.length := by
  induction h with
  | refl => exact hpos
  | step _ ih => rw [refineFibers_length]; omega

theorem Refines.volume {n k A : ℕ} {fs : List (List (Field β n))} {gs : List (List (Field β k))}
    (h : Refines fs gs) (encode : β → List (Fin (A+4))) (W B : ℕ)
    (hlen : ∀ x, (encode x).length = W) (hrows : ∀ rows ∈ fs, rows.length = B) :
    (stream encode gs).length = (stream encode fs).length := by
  induction h with
  | refl => rfl
  | step h ih =>
    exact (stream_refine_length encode W B hlen _ (h.row_length B hrows)).trans (ih hrows)

end IntegerMultBounds.MathlibTM2.Routing.DyadicFieldRefinement
