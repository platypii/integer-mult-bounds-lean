module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSliceDecode
public import IntegerMultBounds.MathlibTM2.Mult.ToeplitzShortConv

/-! # Compact an upper Toeplitz result into the next stage's raw operand stream

The generic slice program selects the first L ring coefficients in descending
order. It preserves the padded source and all counts, and prefixes compact rows
onto an arbitrary destination suffix. Record-symbol counts are supplied here;
the closed cell caller must generate and charge those dimensions.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.ToeplitzInverse
  IntegerMultBounds.Spec.SignedRingProduct Finset

/-- Compact rows are in upper-output order i=0,...,L-1. -/
def upperRows (q l M L : ℕ) (X V : ℕ → List GaussianInt) : List GaussianInt :=
  sliceStream M 0 L (fun n => coeff q l (X n) (V n).reverse)

theorem upper_records_disk {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q)) :
    ∀ n < M, DiskGrid q (fun c => (coeff q l (X n) (V n).reverse c).re)
      (fun c => (coeff q l (X n) (V n).reverse c).im) := by
  intro n hn
  apply coeff_diskGrid
  · simpa [hlenX n hn, hlenV n hn] using hpad
  · exact hX n hn
  · intro z hz
    exact hV n hn z (List.mem_reverse.mp hz)

/-- Cropped words remain normalized S1 operands, with no rescaling or new range oracle. -/
theorem upperRows_disk {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q)) :
    ∀ z ∈ upperRows q l M L X V, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  exact sliceStream_disk (by omega) _ (upper_records_disk hpad X V hlenX hlenV hX hV)

/-- Compaction changes the row stride from the ring size to L, without changing the stage error. -/
theorem upperRows_error {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w)
    (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (i : Fin L) :
    ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
        (((cstream A w (upperRows q l M L X V) ++ tail).drop
          ((n * L + i.val) * w)).take w)) -
      upper L (fun k => value q (block (X n) k)) (fun k => value q (block (V n) k)) i.val‖ ≤
        2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hsize : 0 + L ≤ 2 ^ l := by omega
  dsimp only [upperRows]
  rw [sliceStream_word hA hw hsize _ (upper_records_disk hpad X V hlenX hlenV hX hV) tail n hn i]
  simpa only [Nat.zero_add] using
    upper_coeff_error q l L (X n) (V n) (hlenX n hn) (hlenV n hn) hpad i.val i.isLt

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- Execute prefix selection on the actual padded upper result. Source, counts,
scratch and arbitrary source/destination suffixes are restored. Only dst gains compact rows. -/
theorem upper_crop_exec
    {dst batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [dst, batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    {q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hbatch : (S.R batch).length = M)
    (hsrc : S.R src = cstream A w (Fixed.result q l M X (fun n => (V n).reverse)) ++ tail)
    (hskip : S.R skip = []) (hm : (S.R mR).length = L)
    (hword : (S.R wordR).length = w) (hrecord : (S.R recordSymbols).length = 2 ^ l * w)
    (hclean : ∀ k ∈ [batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp], S.R k = []) :
    let SF := { S with R := (Function.update S.R dst
      (cstream A w (upperRows q l M L X V) ++ S.R dst)) }
    ∃ v', v'.user = v.user ∧
      Exec body (correlationBatch batch batchSaved skip savedSkip mR recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S)
        (M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) + 8) (mk v' SF) ∧
      ∀ n < M, ∀ i : Fin L,
        ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
            (((SF.R dst).drop ((n * L + i.val) * w)).take w)) -
          upper L (fun k => value q (block (X n) k)) (fun k => value q (block (V n) k)) i.val‖ ≤
            2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  dsimp only
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hsize : 0 + L ≤ 2 ^ l := by omega
  obtain ⟨v', hu, he⟩ := sliceBatch_rpStream_exec (body := body) hreg w 0 L (2 ^ l) M hsize
    (fun n => coeff q l (X n) (V n).reverse) v S tail hbatch hsrc (by simp [hskip]) hm hword hrecord hclean
  refine ⟨v', hu, by simpa only [upperRows, Nat.mul_zero, Nat.zero_mul, Nat.zero_add] using he, ?_⟩
  intro n hn i
  simpa only [Function.update_self] using upperRows_error hA hw hpad X V hlenX hlenV hX hV (S.R dst) n hn i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
