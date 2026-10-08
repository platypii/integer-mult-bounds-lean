import IntegerMultBounds.Machine.FlatAffineScalingReady

/-! Canonical finite-array output for actual initialized and normalized affine
scaling. The next operation may refactor the same literal source word into a
different prefix/target/suffix split without copying it or adding address keys. -/
namespace IntegerMultBounds.Machine.FlatAffineScalingArray
open Networks
open ActualAffineScaling (modulus)
noncomputable section
variable {P B b : ℕ}

private theorem overwrite (f : ℤ → Fin 4) (p : ℤ) (xs ys : List (Fin 4))
    (hlen : xs.length = ys.length) : putWord (putWord f p xs) p ys = putWord f p ys := by
  funext z
  by_cases hi : p ≤ z ∧ z < p+ys.length
  · let i := (z-p).toNat
    have he : p+(i : ℤ) = z := by dsimp [i]; omega
    have hb : i < ys.length := by dsimp [i]; omega
    rw [← he,WordSegments.get _ _ _ i hb,WordSegments.get _ _ _ i hb]
  · rw [putWord_outside _ p z ys (by omega),putWord_outside _ p z ys (by omega)]
    exact putWord_outside f p z xs (by omega)

def array {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) : Fin (P*(modulus b*B)) → Fin 4 :=
  fun i => (FlatAffineScalingNormalize.word hr a)[i.val]'(by
    rw [FlatAffineScalingNormalize.word_length]; exact i.isLt)

theorem array_word {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) :
    List.ofFn (array hr a) = FlatAffineScalingNormalize.word hr a := by
  apply List.ext_getElem
  · simp [FlatAffineScalingNormalize.word_length]
  · intro i hi hj; simp [array]

def coordinate (r : ℚ) (y : Fin (modulus b)) : Fin (modulus b) :=
  let _ : NeZero (modulus b) := ⟨Nat.ne_of_gt (ActualAffineScaling.modulus_pos b)⟩
  ⟨(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val,ZMod.val_lt _⟩

/-- The new canonical array has exactly the prescribed scaling permutation. -/
theorem array_entry {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (i : Fin P) (y : Fin (modulus b)) (j : Fin B) :
    array hr a (FiberLayoutData.index i (coordinate r y) j) = a (FiberLayoutData.index i y j) := by
  have hidx : i.val*(modulus b*B)+(Swap.Modular.ratMod (modulus b) r*(y.val : ZMod (modulus b))).val*B+j.val <
      (FlatAffineScalingNormalize.word hr a).length := by
    rw [FlatAffineScalingNormalize.word_length]
    simpa only [FiberLayoutData.index_val,coordinate] using (FiberLayoutData.index i (coordinate r y) j).isLt
  have hh := FlatAffineScalingReady.output_symbol hr a [] [] [] (fun _ => blank) (fun _ => blank) i y j
  rw [(FlatAffineScalingReady.output_payload hr a [] [] [] (fun _ => blank) (fun _ => blank)).1] at hh
  have hg := WordSegments.get (putWord (fun _ => blank) 0 (List.ofFn a)) 0
    (FlatAffineScalingNormalize.word hr a) _ hidx
  simp only [zero_add] at hg
  rw [hg] at hh
  simpa only [array,FiberLayoutData.index_val,coordinate] using hh

/-- The returned original source is a canonical new array over the original
background; the old input-word overlay disappears completely. -/
theorem output_source {r : ℚ} (hr : Shared50AffineCoefficients.ScaleOccurs r)
    (a : Fin (P*(modulus b*B)) → Fin 4) (bs qs ns : List Bool) (source dest : ℤ → Fin 4) :
    (FlatAffineScalingReady.output hr a bs qs ns source dest).tape (FlatAffineScaling.sourceSlot r) =
      putWord source 0 (List.ofFn (array hr a)) := by
  rw [(FlatAffineScalingReady.output_payload hr a bs qs ns source dest).1,array_word,overwrite]
  simp [FlatAffineScalingNormalize.word_length]

end
end IntegerMultBounds.Machine.FlatAffineScalingArray
