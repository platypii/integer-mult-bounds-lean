module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReciprocal

/-! Evaluate the matrices used for the successive columns of a valid pivot itinerary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback

variable {d : ℕ} (p w : ℕ)
local notation "R" => ZMod (p^(w+1))

/-- Each row shares one multiplier across all its entries. -/
def clearColumn (k pivot : Fin d) (m : Matrix (Fin d) (Fin d) R) : Matrix (Fin d) (Fin d) R :=
  let inv := pivotReciprocal p (m pivot k) w
  fun i =>
    if i = k then m pivot else
      let row := m (Equiv.swap k pivot i)
      let c := row k * inv
      fun j => row j - c * m pivot j

theorem clearColumn_eq (hp : p.Prime) (k pivot : Fin d) (m : Matrix (Fin d) (Fin d) R)
    (unit : IsUnit (m pivot k)) :
    clearColumn p w k pivot m = stepOp k pivot m (Ring.inverse (m pivot k)) * m := by
  ext i j
  rw [stepOp_apply]
  by_cases h : i = k <;> simp [clearColumn,h,pivotReciprocal_eq hp w _ unit]

def itineraryEntries (pivot : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) R) :
    ℕ → Matrix (Fin d) (Fin d) R
  | 0 => m
  | n+1 =>
    let current := itineraryEntries pivot m n
    if h : n < d then clearColumn p w ⟨n,h⟩ (pivot ⟨n,h⟩) current else current

theorem itineraryEntries_eq (hp : p.Prime) (pivot : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) R)
    (n : ℕ) (valid : Itinerary.Valid pivot m n) :
    itineraryEntries p w pivot m n = Itinerary.run pivot m n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨prev,unit⟩ := (Itinerary.valid_succ pivot m n).mp valid
    simp only [itineraryEntries,ih prev]
    split <;> rename_i h
    · exact (clearColumn_eq p w hp _ _ _ (unit h).2).trans (Itinerary.run_succ pivot m n h).symm
    · exact (Itinerary.run_succ_of_not pivot m n h).symm

end IntegerMultBounds.MathlibTM2.Cover.Fallback
