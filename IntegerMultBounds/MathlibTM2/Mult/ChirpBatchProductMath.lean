module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatchProduct
public import IntegerMultBounds.MathlibTM2.Mult.ChirpProductMath

/-! # Analytic semantics of the shared chirp correlation tape

The actual word at flattened position `nm+b` is the same signed numerator as in the
single-block bridge. Therefore all blocks share one product call without changing the
correlation interpretation or its rounding error.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- Shared extraction emits exactly `M*m` coefficients, including empty batches. -/
theorem correlationStream_length {r : ℕ} (M m : ℕ) (hsize : 4 * m ≤ r)
    (X : ℕ → Fin r → GaussianInt) : (correlationStream M m X).length = M * m := by
  rw [correlationStream_eq M m hsize X]
  exact length_rpStream _ _

/-- Signed decoding at the actual output position of a shared batch. -/
theorem correlationBatchTape_coeff {A : ℕ} (hA : 4 ≤ A) (p l w M m : ℕ)
    (hw : p + 2 ≤ w) (hl : 4 * m ≤ 2 ^ l) (X Y : ℕ → List GaussianInt)
    (hxy : ∀ n < M, (X n).length + (Y n).length ≤ 2 ^ l + 1)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (b : Fin m) :
    decodeWord (((cstream A w (correlationStream M m (fun n => coeff p l (X n) (Y n))) ++ tail).drop
      ((n * m + b.val) * w)).take w) =
        coeff p l (X n) (Y n) ⟨4 * m - 1 - b.val, by have := b.isLt; omega⟩ := by
  let Z := fun n => coeff p l (X n) (Y n)
  have hj : n * m + b.val < (correlationStream M m Z).length := by
    rw [correlationStream_length M m hl Z]
    have hmul := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hn)
    rw [Nat.succ_mul] at hmul
    have := b.isLt
    omega
  rw [cstream_word w _ tail _ hj, decodeWord_csyms hA]
  have he := correlationStream_get M m hl Z n hn b
  rw [List.getElem?_eq_getElem hj] at he
  rw [Option.some.inj he]
  obtain ⟨hre, him⟩ := coeff_fits p l w (X n) (Y n) (hxy n hn) hw (hX n hn) (hY n hn)
    ⟨4 * m - 1 - b.val, by have := b.isLt; omega⟩
  rw [hre, him]

/-- Every decoded batch word agrees with the analytic ring correlation under the explicit
operand-production interface. -/
theorem correlationBatchTape_chirpRingCorr {s t A : ℕ} (hA : 4 ≤ A) (p l w M m : ℕ)
    (hw : p + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l) (X Y : ℕ → List GaussianInt)
    (hxy : ∀ n < M, (X n).length + (Y n).length ≤ 2 ^ l + 1)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ) (u : ZMod s → ℂ)
    (hx : ∀ n < M, ∀ i : Fin (2 ^ l), value p (block (X n) i) = chirpRecIn (t := t) m rd gt u n i)
    (hy : ∀ n < M, ∀ i : Fin (2 ^ l), value p (block (Y n) i) = chirpRecK m kt n i)
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (b : Fin m) :
    (4 * (2 ^ l : ℕ) : ℂ) * value p (decodeWord
      (((cstream A w (correlationStream M m (fun n => coeff p l (X n) (Y n))) ++ tail).drop
        ((n * m + b.val) * w)).take w)) = chirpRingCorr (t := t) p m l rd gt kt u (n * m) b.val := by
  rw [correlationBatchTape_coeff hA p l w M m hw (by omega) X Y hxy hX hY tail n hn b]
  have he := correlationTape_chirpRingCorr hA p l w m hw hm hl (X n) (Y n) (hxy n hn)
    (hX n hn) (hY n hn) rd gt kt u n (hx n hn) (hy n hn) tail b.val b.isLt
  rwa [correlationTape_coeff hA p l w m hw (by omega) (X n) (Y n) (hxy n hn)
    (hX n hn) (hY n hn) tail b.val b.isLt] at he

/-- The correlation error is independent of the number of records sharing the product call. -/
theorem correlationBatchTape_chirpCorr_err {s t A : ℕ} (hA : 4 ≤ A) (p l w M m : ℕ)
    (hw : p + 2 ≤ w) (hm : 1 ≤ m) (hl : 7 * m ≤ 2 ^ l) (X Y : ℕ → List GaussianInt)
    (hxy : ∀ n < M, (X n).length + (Y n).length ≤ 2 ^ l + 1)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (hY : ∀ n < M, ∀ z ∈ Y n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p))
    (rd : ℂ → ℂ) (gt : ℕ → ℕ → ℝ) (kt : ℕ → ℤ → ℝ) (u : ZMod s → ℂ)
    (hx : ∀ n < M, ∀ i : Fin (2 ^ l), value p (block (X n) i) = chirpRecIn (t := t) m rd gt u n i)
    (hy : ∀ n < M, ∀ i : Fin (2 ^ l), value p (block (Y n) i) = chirpRecK m kt n i)
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (b : Fin m) :
    ‖(4 * (2 ^ l : ℕ) : ℂ) * value p (decodeWord
      (((cstream A w (correlationStream M m (fun n => coeff p l (X n) (Y n))) ++ tail).drop
        ((n * m + b.val) * w)).take w)) - chirpCorr (t := t) m rd gt kt u (n * m) b.val‖ ≤
      8 * (2 : ℝ) ^ l / (2 : ℝ) ^ p := by
  rw [correlationBatchTape_chirpRingCorr hA p l w M m hw hm hl X Y hxy hX hY
    rd gt kt u hx hy tail n hn b]
  exact chirpRingCorr_err p m l hm hl rd gt kt u n b.val b.isLt

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
