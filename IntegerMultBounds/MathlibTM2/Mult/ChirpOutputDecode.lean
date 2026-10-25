module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputRound
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode

/-! # Exact decoding of the finished chirp output tape

The signed bounds apply after precision reduction, so the rounded/cropped tape
returns the modeled numerator without modular aliasing at every original index.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Spec.SignedRingProduct

/-- Decode a signed coefficient under the strict fit used by the product stages. -/
theorem decodeWord_of_fits {A w : ℕ} (hA : 4 ≤ A) (hw : 1 ≤ w)
    (x : GaussianInt) (hx : Fits w x) : decodeWord (csyms A w x) = x := by
  rw [decodeWord_csyms hA,
    compValue_compWord hw (abs_lt.mp hx.1).1.le (abs_lt.mp hx.1).2,
    compValue_compWord hw (abs_lt.mp hx.2).1.le (abs_lt.mp hx.2).2]

/-- Read an actual finished word, including when the last generated block is partial. -/
theorem chirpOutputFinished_coeff {A p q : ℕ} (hA : 4 ≤ A) (hpq : p ≤ q)
    (l Γ t : ℕ) (xs : List GaussianInt)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 8 * (2 : ℝ) ^ (l + Γ))
    (tail : List (Fin (A + 4))) (j : ℕ) (hjt : j < t) (hjx : j < xs.length) :
    decodeWord (((cstream A (p + l + Γ + 5) ((xs.take t).map (tdivN (q - p))) ++ tail).drop
      (j * (p + l + Γ + 5))).take (p + l + Γ + 5)) = tdivN (q - p) xs[j] := by
  have hj : j < ((xs.take t).map (tdivN (q - p))).length := by simp; omega
  rw [cstream_word _ _ tail j hj, List.getElem_map, List.getElem_take]
  exact decodeWord_of_fits hA (by omega) _
    (chirpRounded_fits hpq l Γ _ le_rfl _ (hxs _ (List.getElem_mem hjx)))

/-- The finished tape implements p-grid rounding of the q-grid output numerators. -/
theorem chirpOutputFinished_value {A p q : ℕ} (hA : 4 ≤ A) (hpq : p ≤ q)
    (l Γ t : ℕ) (xs : List GaussianInt)
    (hxs : ∀ x ∈ xs, ‖value q x‖ ≤ 8 * (2 : ℝ) ^ (l + Γ))
    (tail : List (Fin (A + 4))) (j : ℕ) (hjt : j < t) (hjx : j < xs.length) :
    value p (decodeWord (((cstream A (p + l + Γ + 5) ((xs.take t).map (tdivN (q - p))) ++ tail).drop
      (j * (p + l + Γ + 5))).take (p + l + Γ + 5))) = NLogN.rhoC p (value q xs[j]) := by
  rw [chirpOutputFinished_coeff hA hpq l Γ t xs hxs tail j hjt hjx, value_round_precision hpq]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
