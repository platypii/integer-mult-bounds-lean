module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBatch

/-! # Decoding and range preservation for compacted convolution slices

A selected stream has row stride m, not the padded ring stride r. Selection
copies numerators exactly and retains their disk-grid bounds for the next S1 call.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.Spec.SignedRingProduct Finset

@[simp] theorem sliceStream_length {r : ℕ} (M a m : ℕ) (hsize : a + m ≤ r)
    (X : ℕ → Fin r → GaussianInt) : (sliceStream M a m X).length = M * m := by
  rw [sliceStream_eq M a m hsize X]
  exact length_rpStream _ _

/-- A compacted numerator needs no new range hypothesis before a subsequent product. -/
theorem sliceStream_disk {r p M a m : ℕ} (hsize : a + m ≤ r)
    (X : ℕ → Fin r → GaussianInt)
    (hX : ∀ n < M, DiskGrid p (fun c => (X n c).re) (fun c => (X n c).im)) :
    ∀ z ∈ sliceStream M a m X, z.re ^ 2 + z.im ^ 2 ≤ (2 : ℤ) ^ (2 * p) := by
  intro z hz
  rw [sliceStream_eq M a m hsize X] at hz
  simp only [rpStream] at hz
  obtain ⟨n, hn, hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hz
  exact hX n (List.mem_range.mp hn) _

/-- Decode the compacted row directly in front of any original destination suffix. -/
theorem sliceStream_word {A r p w M a m : ℕ} (hA : 4 ≤ A) (hw : p + 2 ≤ w)
    (hsize : a + m ≤ r) (X : ℕ → Fin r → GaussianInt)
    (hX : ∀ n < M, DiskGrid p (fun c => (X n c).re) (fun c => (X n c).im))
    (tail : List (Fin (A + 4))) (n : ℕ) (hn : n < M) (i : Fin m) :
    decodeWord (((cstream A w (sliceStream M a m X) ++ tail).drop
      ((n * m + i.val) * w)).take w) = X n ⟨a + m - 1 - i.val, by have := i.isLt; omega⟩ := by
  have hj : n * m + i.val < (sliceStream M a m X).length := by
    rw [sliceStream_length M a m hsize X]
    have hmul := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hn)
    rw [Nat.succ_mul] at hmul
    have hi := i.isLt
    omega
  rw [cstream_word w _ tail _ hj, decodeWord_csyms hA]
  have he := sliceStream_get M a m hsize X n hn i
  rw [List.getElem?_eq_getElem hj] at he
  rw [Option.some.inj he]
  obtain ⟨hre, him⟩ := (hX n hn).fits hw ⟨a + m - 1 - i.val, by have := i.isLt; omega⟩
  rw [hre, him]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
