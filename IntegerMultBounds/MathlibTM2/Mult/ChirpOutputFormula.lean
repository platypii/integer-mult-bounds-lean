module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputTables
public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandProduct
public import IntegerMultBounds.MathlibTM2.Mult.ChirpBlockCount

/-! # The integer output formula agrees with the analytic chirp map

Decode the actual shared correlation tape at each global output index. Applying the
proved integer shifts, real products and final truncation gives exactly `chirpAR`.
This is the arithmetic bridge; execution of those output operations is separate.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Fast

/-- Every original output index lies in the generated ceiling batch. -/
theorem chirpOutput_block_lt {t m k : ℕ} (hk : k < t) :
    k / m < chirpBlockCount t m := by
  have hdiv := Nat.div_le_div_right (by omega : k ≤ t - 1) (c := m)
  unfold chirpBlockCount
  omega

/-- Integer postprocessing of one physical correlation word. -/
def chirpOutputWord (p q l Γ : ℕ) (c : GaussianInt) (e a : ℤ) : GaussianInt :=
  tdivN (q - p) (chirpOutputNumerator q l Γ c e a)

/-- Abstract scalar form of the analytic output-stage bridge. -/
theorem chirpOutputWord_eq {s t : ℕ} [NeZero s] [NeZero t]
    {p q : ℕ} (hpq : p ≤ q) (m l Γ : ℕ)
    (corr : (ZMod s → ℂ) → ℕ → ℕ → ℂ) (u : ZMod s → ℂ)
    (c : GaussianInt) (e : ℕ → ℤ) (a : ℤ) (k : ZMod t)
    (hc : (4 * (2 ^ l : ℕ) : ℂ) * value (q + 1) c = corr u (k.val / m * m) (k.val % m)) :
    value p (chirpOutputWord p q l Γ c (e (k.val % m)) a) =
      chirpAG (t := t) p m Γ (rhoC q) corr
        (fun _ b => (e b : ℝ) / 2 ^ q) ((a : ℝ) / 2 ^ q) u k := by
  rw [chirpOutputWord, value_chirpOutput hpq, hc]
  rfl

/-- Scalar correctness for the actual generated-operand shared correlation tape. -/
theorem chirpOutputWord_chirpAR {s t A : ℕ} [NeZero s] [NeZero t]
    (hA : 4 ≤ A) (hst : s < t) (α p q l w m Γ : ℕ)
    (hα : 0 < α) (hq : 13 ≤ q) (hpq : p ≤ q) (hw : q + 1 + 2 ≤ w)
    (hm : 0 < m) (hl : 7 * m ≤ 2 ^ l)
    (u : ZMod s → GaussianInt) (hu : ∀ j, ‖value q (u j)‖ ≤ 1)
    (e : ℕ → ℤ) (a : ℤ) (tail : List (Fin (A + 4))) (k : ZMod t) :
    let X := fun n => chirpOperandX s t q m n (chirpInputNumerators s t α q m) u
    let Y := fun n => chirpOperandY m n (chirpKernelNumerators s t α q m)
    let tape := cstream A w (correlationStream (chirpBlockCount t m) m
      (fun n => coeff (q + 1) l (X n) (Y n))) ++ tail
    value p (chirpOutputWord p q l Γ (decodeWord ((tape.drop (k.val * w)).take w))
      (e (k.val % m)) a) =
      chirpAR (s := s) (t := t) p (q + 1) m l Γ (rhoC q)
        (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q)
        (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q)
        (fun _ b => (e b : ℝ) / 2 ^ q) ((a : ℝ) / 2 ^ q) (fun j => value q (u j)) k := by
  apply chirpOutputWord_eq hpq m l Γ
  have hbatch := correlationBatchTape_chirpRingCorr (s := s) (t := t) hA (q + 1) l w
    (chirpBlockCount t m) m hw hm hl
    (fun n => chirpOperandX s t q m n (chirpInputNumerators s t α q m) u)
    (fun n => chirpOperandY m n (chirpKernelNumerators s t α q m))
    (fun n _ => chirpOperands_length s t q m n l _ _ u hl)
    (fun n _ z hz => chirpOperandX_disk hst α q m hα hq u hu n z hz)
    (fun n _ z hz => chirpOperandY_disk hst α q m hα hq u hu n z hz)
    (rhoC q) (fun k0 a => (chirpTableG s t α q m k0 a : ℝ) / 2 ^ q)
    (fun k0 a => (chirpTableK s t α q m k0 a : ℝ) / 2 ^ q) (fun j => value q (u j))
    (by intro n hn i; simpa only [chirpInputNumerators, Int.cast_natCast] using value_chirpOperandX q m n i (chirpInputNumerators s t α q m) u)
    (by intro n hn i; simpa only [chirpKernelNumerators, Int.cast_natCast] using value_chirpOperandY q m n i (chirpKernelNumerators s t α q m))
    tail (k.val / m) (chirpOutput_block_lt k.val_lt) ⟨k.val % m, Nat.mod_lt _ hm⟩
  simpa only [Nat.div_add_mod'] using hbatch

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
