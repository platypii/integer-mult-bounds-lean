import IntegerMultBounds.Machine.ActiveRepairDestinationPatchOverwrite

/-! Fixed-width address patches retain all bits outside their runtime interval.
The word definition is identified with the actual physical tape overwrite. -/
namespace IntegerMultBounds.Machine.ActiveRepairDestinationPatchData
noncomputable section
variable {a : ℕ}

def patch (xs : List Bool) (start : ℕ) (ys : List Bool) : List Bool :=
  (List.range xs.length).map fun j =>
    if start≤j ∧ j<start+ys.length then ys.getD (j-start) false else xs.getD j false

@[simp] theorem patch_length (xs : List Bool) (start : ℕ) (ys : List Bool) :
    (patch xs start ys).length=xs.length := by simp [patch]

theorem patch_bit (xs : List Bool) (start : ℕ) (ys : List Bool) (j : ℕ) (hj : j<xs.length) :
    (patch xs start ys).getD j false=
      if start≤j ∧ j<start+ys.length then ys.getD (j-start) false else xs.getD j false := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by simpa using hj)]
  simp [patch]

theorem outside (xs : List Bool) (start : ℕ) (ys : List Bool) (j : ℕ)
    (hj : j<xs.length) (hout : j<start ∨ start+ys.length≤j) :
    (patch xs start ys).getD j false=xs.getD j false := by
  rw [patch_bit xs start ys j hj,ite_eq_right (by omega)]

theorem inside (xs : List Bool) (start : ℕ) (ys : List Bool)
    (hfit : start+ys.length≤xs.length) (j : ℕ) (hj : j<ys.length) :
    (patch xs start ys).getD (start+j) false=ys.getD j false := by
  rw [patch_bit xs start ys (start+j) (by omega),ite_eq_left (by omega),Nat.add_sub_cancel_left]

theorem tape (f : ℤ → Fin (a+4)) (p : ℤ) (xs : List Bool) (start : ℕ) (ys : List Bool)
    (hfit : start+ys.length≤xs.length) :
    putWord (putWord f p (xs.map bitSymbol)) (p+start) (ys.map bitSymbol)=
      putWord f p ((patch xs start ys).map bitSymbol) := by
  funext z
  by_cases hlow : z<p
  · rw [putWord_outside _ _ _ _ (Or.inl (by omega)),
        putWord_outside _ _ _ _ (Or.inl hlow),putWord_outside _ _ _ _ (Or.inl hlow)]
  by_cases hhigh : p+xs.length≤z
  · rw [putWord_outside _ _ _ _ (Or.inr (by simp only [List.length_map]; omega)),
        putWord_outside _ _ _ _ (Or.inr (by simpa using hhigh)),
        putWord_outside _ _ _ _ (Or.inr (by simpa using hhigh))]
  let j := (z-p).toNat
  have hz : z=p+j := by dsimp [j]; omega
  have hj : j<xs.length := by omega
  rw [hz,Gather.putWord_getD f p (patch xs start ys) j (by simpa using hj),patch_bit xs start ys j hj]
  by_cases hin : start≤j ∧ j<start+ys.length
  · rw [ite_eq_left hin]
    have he : p+(j : ℤ)=(p+start)+((j-start : ℕ) : ℤ) := by omega
    rw [he,Gather.putWord_getD _ _ ys (j-start) (by omega)]
  · rw [ite_eq_right hin,putWord_outside _ _ _ _ (by simp only [List.length_map]; omega),
        Gather.putWord_getD f p xs j hj]

/-- The entire replacement interval is the literal supplied word. -/
theorem field_inside (xs : List Bool) (start : ℕ) (ys : List Bool)
    (hfit : start+ys.length≤xs.length) :
    Gather.field (patch xs start ys) start ys.length=ys := by
  have he : Gather.field ys 0 ys.length=ys := by
    rw [IntegerMultBounds.Compact.PowerTwo.field_take ys ys.length (le_refl _),List.take_length]
  conv_rhs => rw [←he]
  unfold Gather.field
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  simp only [zero_add]
  exact inside xs start ys hfit j hj

/-- A disjoint original field is unchanged, including when other fields have
already been patched. -/
theorem field_outside (xs : List Bool) (start : ℕ) (ys : List Bool) (offset width : ℕ)
    (hfit : offset+width≤xs.length)
    (hdis : offset+width≤start ∨ start+ys.length≤offset) :
    Gather.field (patch xs start ys) offset width=Gather.field xs offset width := by
  unfold Gather.field
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range] at hj
  exact outside xs start ys (offset+j) (by omega) (by omega)

theorem disjoint_commute (xs : List Bool) (s t : ℕ) (ys zs : List Bool)
    (hdis : s+ys.length≤t ∨ t+zs.length≤s) :
    patch (patch xs s ys) t zs=patch (patch xs t zs) s ys := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hx : j<xs.length := by simpa using hj
    have hd : (patch (patch xs s ys) t zs).getD j false=
        (patch (patch xs t zs) s ys).getD j false := by
      rw [patch_bit (patch xs s ys) t zs j (by simpa using hx),patch_bit xs s ys j hx,
        patch_bit (patch xs t zs) s ys j (by simpa using hx),patch_bit xs t zs j hx]
      by_cases hy : s≤j ∧ j<s+ys.length
      · have hz : ¬(t≤j ∧ j<t+zs.length) := by omega
        simp [hy,hz]
      · by_cases hz : t≤j ∧ j<t+zs.length <;> simp [hy,hz]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,
      List.getElem?_eq_getElem hj',Option.getD_some] using hd

end
end IntegerMultBounds.Machine.ActiveRepairDestinationPatchData
