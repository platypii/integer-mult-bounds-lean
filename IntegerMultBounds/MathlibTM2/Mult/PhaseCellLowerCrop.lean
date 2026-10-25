module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellUpperCropSetup

/-! # Compact lower-product rows through the shared coefficient selector

The selector reverses each selected row. Reading position L-1-i gives lower
coordinate i; no extra reversal or uncharged reformatting is assumed.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.NLogN.ToeplitzInverse Finset

def lowerRows (q l M L : ℕ) (X V : ℕ → List GaussianInt) : List GaussianInt :=
  sliceStream M 0 L (fun n => coeff q l (X n) (V n))

theorem lower_records_disk {q l M L : ℕ} (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q)) :
    ∀ n < M, DiskGrid q (fun c => (coeff q l (X n) (V n) c).re)
      (fun c => (coeff q l (X n) (V n) c).im) := by
  intro n hn
  apply coeff_diskGrid
  · simpa [hlenX n hn, hlenV n hn] using hpad
  · exact hX n hn
  · exact hV n hn

/-- The decoded lower output has compact stride L and reversed row coordinates. -/
theorem lowerRows_error {A q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w)
    (hpad : L + L ≤ 2 ^ l + 1) (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (i : Fin L) :
    ‖((2 ^ l : ℕ) : ℂ) * value q (decodeWord
      (((cstream A w (lowerRows q l M L X V) ++ tail).drop
        ((n * L + (L - 1 - i.val)) * w)).take w)) -
      lower (fun k => value q (block (X n) k)) (fun k => value q (block (V n) k)) i.val‖ ≤
      2 * (2 ^ l : ℕ) / (2 : ℝ) ^ q := by
  have hr : 1 ≤ 2 ^ l := Nat.one_le_two_pow
  have hsize : 0 + L ≤ 2 ^ l := by omega
  dsimp only [lowerRows]
  rw [sliceStream_word hA hw hsize _ (lower_records_disk hpad X V hlenX hlenV hX hV)
    tail n hn ⟨L - 1 - i.val, by omega⟩]
  have hi : 0 + L - 1 - (L - 1 - i.val) = i.val := by omega
  simp only [hi]
  rw [lower_convolution]
  exact coeff_err q l (X n) (V n) (by simpa [hlenX n hn, hlenV n hn] using hpad) _

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- The shared generated-count crop executes on lower results too. There is no
new selection loop, supplied reversed operand or supplied ring-symbol counter. -/
theorem lowerCropFromDimensions_exec
    {lR dst batch batchSaved skip savedSkip mR recordSaved wordR recordSymbols src acc current savedSource saved buf tmp : Fin T}
    (hreg : [lR, dst, batch, batchSaved, skip, savedSkip, mR, recordSaved, wordR, recordSymbols, src,
      acc, current, savedSource, saved, buf, tmp].Nodup)
    {q l w M L : ℕ} (hA : 4 ≤ A) (hw : q + 2 ≤ w) (hpad : L + L ≤ 2 ^ l + 1)
    (X V : ℕ → List GaussianInt)
    (hlenX : ∀ n < M, (X n).length = L) (hlenV : ∀ n < M, (V n).length = L)
    (hX : ∀ n < M, ∀ z ∈ X n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (hV : ∀ n < M, ∀ z ∈ V n, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q))
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A + 4)))
    (hl : (S.R lR).length = l) (hbatch : (S.R batch).length = M)
    (hsrc : S.R src = cstream A w (Fixed.result q l M X V) ++ tail)
    (hskip : S.R skip = []) (hm : (S.R mR).length = L) (hword : (S.R wordR).length = w)
    (hclean : ∀ k ∈ [recordSymbols, batchSaved, acc, savedSource, savedSkip, recordSaved, current, saved, buf, tmp],
      S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ M * (20 * L * w + 19 * L + 6 * 2 ^ l * w + 23) +
        4 * w + 6 * 2 ^ l * w + 9 * l + 22 ∧
      Exec body (upperCropFromDimensions lR batch batchSaved skip savedSkip mR recordSaved wordR
        recordSymbols src acc current savedSource saved buf tmp dst) (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (cstream A w (lowerRows q l M L X V) ++ S.R dst)) }) := by
  have hlenR : ∀ n < M, ((V n).reverse).length = L := by simpa using hlenV
  have hR : ∀ n < M, ∀ z ∈ (V n).reverse,
      z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * q) := by
    intro n hn z hz
    exact hV n hn z (List.mem_reverse.mp hz)
  obtain ⟨v', n, hu, hn, he, _⟩ := upperCropFromDimensions_exec (body := body) hreg hA hw hpad
    X (fun n => (V n).reverse) hlenX hlenR hX hR v S tail hl hbatch
    (by simpa only [List.reverse_reverse] using hsrc) hskip hm hword hclean
  refine ⟨v', n, hu, hn, ?_⟩
  simpa only [upperRows, lowerRows, List.reverse_reverse] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
