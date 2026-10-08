import IntegerMultBounds.Machine.InjectivePlacement

/-! Reading a replaced bank cell by cell: at an active slot the replacement's
tape and head appear, elsewhere the original bank is unchanged. With these,
an exact contract placed by an injective slot map yields an exact contract
on the whole bank once the two banks are compared index by index. -/

namespace IntegerMultBounds.Machine.Placement

variable {s u t a : ℕ}

theorem replace_tape_active (e : Fin (s + u) ≃ Fin t) (v : Tapes t a) (w : Tapes s a) (i : Fin s) :
    (replace e v w).tape (e (Fin.castAdd u i)) = w.tape i := by
  simp [replace, combine_tape_active]

theorem replace_head_active (e : Fin (s + u) ≃ Fin t) (v : Tapes t a) (w : Tapes s a) (i : Fin s) :
    (replace e v w).head (e (Fin.castAdd u i)) = w.head i := by
  simp [replace, combine_head_active]

theorem replace_tape_other (e : Fin (s + u) ≃ Fin t) (v : Tapes t a) (w : Tapes s a) (x : Fin t)
    (hx : ∀ i : Fin s, e (Fin.castAdd u i) ≠ x) : (replace e v w).tape x = v.tape x := by
  obtain ⟨y, rfl⟩ : ∃ y, e y = x := ⟨e.symm x, by simp⟩
  revert hx
  refine Fin.addCases (fun i hx => ?_) (fun j hx => ?_) y
  · exact absurd rfl (hx i)
  · simp [replace, combine_tape_extra, extra]

theorem replace_head_other (e : Fin (s + u) ≃ Fin t) (v : Tapes t a) (w : Tapes s a) (x : Fin t)
    (hx : ∀ i : Fin s, e (Fin.castAdd u i) ≠ x) : (replace e v w).head x = v.head x := by
  obtain ⟨y, rfl⟩ : ∃ y, e y = x := ⟨e.symm x, by simp⟩
  revert hx
  refine Fin.addCases (fun i hx => ?_) (fun j hx => ?_) y
  · exact absurd rfl (hx i)
  · simp [replace, combine_head_extra, extra]

/-- Two banks agreeing at every head and cell are equal. -/
theorem Tapes.ext' {v w : Tapes t a} (hh : ∀ x, v.head x = w.head x) (ht : ∀ x, v.tape x = w.tape x) :
    v = w := by
  cases v; cases w
  simp only [Tapes.mk.injEq]
  exact ⟨funext hh, funext ht⟩

end IntegerMultBounds.Machine.Placement

namespace IntegerMultBounds.Machine.InjectivePlacement

variable {s u t a : ℕ}

theorem replace_tape_slot (slot : Fin s → Fin t) (hinj : Function.Injective slot) (hsize : s + u = t)
    (v : Tapes t a) (w : Tapes s a) (i : Fin s) :
    (Placement.replace (placement slot hinj hsize) v w).tape (slot i) = w.tape i := by
  rw [← active_slot slot hinj hsize i]
  exact Placement.replace_tape_active _ _ _ _

theorem replace_head_slot (slot : Fin s → Fin t) (hinj : Function.Injective slot) (hsize : s + u = t)
    (v : Tapes t a) (w : Tapes s a) (i : Fin s) :
    (Placement.replace (placement slot hinj hsize) v w).head (slot i) = w.head i := by
  rw [← active_slot slot hinj hsize i]
  exact Placement.replace_head_active _ _ _ _

theorem replace_tape_other (slot : Fin s → Fin t) (hinj : Function.Injective slot) (hsize : s + u = t)
    (v : Tapes t a) (w : Tapes s a) (x : Fin t) (hx : ∀ i, slot i ≠ x) :
    (Placement.replace (placement slot hinj hsize) v w).tape x = v.tape x :=
  Placement.replace_tape_other _ _ _ _ (fun i => by rw [active_slot]; exact hx i)

theorem replace_head_other (slot : Fin s → Fin t) (hinj : Function.Injective slot) (hsize : s + u = t)
    (v : Tapes t a) (w : Tapes s a) (x : Fin t) (hx : ∀ i, slot i ≠ x) :
    (Placement.replace (placement slot hinj hsize) v w).head x = v.head x :=
  Placement.replace_head_other _ _ _ _ (fun i => by rw [active_slot]; exact hx i)

/-- An exact contract placed by an injective slot map, in exact-bank form:
the whole bank before is `v`, and the bank after is determined by comparing
with the replacement at every index. -/
theorem hoare_exact {q : ℕ} {M : Program s q a} {X X' : Tapes s a} {b : ℕ}
    (h : HoareTime M (fun w => w = X) (fun w => w = X') b)
    (slot : Fin s → Fin t) (hinj : Function.Injective slot) (hsize : s + u = t)
    (v v' : Tapes t a) (hv : Placement.active (placement slot hinj hsize) v = X)
    (hv' : Placement.replace (placement slot hinj hsize) v X' = v') :
    HoareTime (Placement.placed M (placement slot hinj hsize)) (fun w => w = v) (fun w => w = v') b := by
  have := Placement.hoare_at h (placement slot hinj hsize) v hv
  exact this.consequence (fun w hw => hw) (fun w ⟨z, hz, hw⟩ => by rw [hw, hz, hv']) le_rfl

end IntegerMultBounds.Machine.InjectivePlacement
