module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputStream

/-! # The output stage uses one E row periodically in flattened correlation order -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast

/-- A flattened output numerator uses the E factor at its offset within the row. -/
theorem chirpOutputNumerators_getElem (q l Γ : ℕ) (blocks : List (List GaussianInt))
    (es : List ℤ) (a : ℤ) (hes : 1 ≤ es.length)
    (hlen : ∀ xs ∈ blocks, xs.length = es.length) (k : ℕ) (hk : k < blocks.flatten.length) :
    (chirpOutputNumerators q l Γ blocks es a)[k]'(by
      rw [chirpOutputNumerators_length q l Γ blocks es a hlen]; exact hk) =
      chirpOutputNumerator q l Γ blocks.flatten[k] (es[k % es.length]'(Nat.mod_lt _ (by omega))) a := by
  have hflat := length_flatten_const blocks hlen
  obtain ⟨j, i, hj, hi, rfl⟩ : ∃ j i, j < blocks.length ∧ i < es.length ∧
      k = es.length * j + i := by
    refine ⟨k / es.length, k % es.length, ?_, Nat.mod_lt _ (by omega), (Nat.div_add_mod k _).symm⟩
    rw [hflat] at hk
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hk)
  have hlenOut : (blocks.flatMap (fun xs =>
      List.zipWith (fun c e => chirpOutputNumerator q l Γ c e a) xs es)).length = blocks.flatten.length :=
    chirpOutputNumerators_length q l Γ blocks es a hlen
  have e1 := getElem_flatMap_len (fun xs =>
      List.zipWith (fun c e => chirpOutputNumerator q l Γ c e a) xs es) es.length blocks
    (fun xs hx => by simp [hlen xs hx]) j i hj hi (by rw [hlenOut]; exact hk)
  have e2 := getElem_flatMap_len id es.length blocks (fun xs hx => by simp [hlen xs hx])
    j i hj hi (by simpa using hk)
  simp only [List.flatMap_id] at e2
  have hmod : (es.length * j + i) % es.length = i := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  simp only [chirpOutputNumerators, hmod]
  rw [e1, List.getElem_zipWith]
  congr 1
  exact e2.symm

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
