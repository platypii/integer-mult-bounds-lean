import IntegerMultBounds.Schoenhage.RingWords

/-! The value a digit step computes. An offset digit `e = h + 2^(Wd-1)` is
shifted to `h` when nonnegative, and to `2^(Wd+1) + h + 2^s - 1` otherwise;
dropping `s` bits and keeping `w` gives the word of `h` truncated toward zero
(`tw_digit`), whenever `w + s ≤ Wd + 1`. -/

namespace IntegerMultBounds.Schoenhage

/-- The natural number a digit step computes before its last cut. -/
def digitVal (Wd s e : ℕ) : ℕ :=
  if 2 ^ (Wd - 1) ≤ e then e - 2 ^ (Wd - 1) else 2 ^ (Wd + 1) + e - 2 ^ (Wd - 1) + (2 ^ s - 1)

/-- A natural number and an integer with the same residue. -/
theorem nat_mod_eq_toNat {n w : ℕ} {z : ℤ} (h : (n : ℤ) % 2 ^ w = z % 2 ^ w) :
    n % 2 ^ w = (z % 2 ^ w).toNat := by
  have hp : (0 : ℤ) < 2 ^ w := by positivity
  rw [← h]
  have : ((n % 2 ^ w : ℕ) : ℤ) = (n : ℤ) % 2 ^ w := by push_cast; rfl
  rw [← this, Int.toNat_natCast]

/-- The digit's value after the shift, as an integer modulo `2^w`. -/
theorem digit_mod {Wd s w e : ℕ} (hW : 1 ≤ Wd) (he : e < 2 ^ Wd) (hws : w + s ≤ Wd + 1) :
    ((digitVal Wd s e / 2 ^ s : ℕ) : ℤ) % 2 ^ w = trunc0 s ((e : ℤ) - 2 ^ (Wd - 1)) % 2 ^ w := by
  set H := 2 ^ (Wd - 1) with hH
  have h2 : 2 ^ Wd = 2 * H := by rw [hH, ← pow_succ']; congr 1; omega
  have h4 : 2 ^ (Wd + 1) = 4 * H := by rw [pow_succ, h2]; ring
  have hs0 : 0 < 2 ^ s := Nat.two_pow_pos s
  by_cases hc : H ≤ e
  · have hd : digitVal Wd s e = e - H := by simp [digitVal, ← hH, hc]
    rw [hd]
    have hn : (0 : ℤ) ≤ (e : ℤ) - (H : ℕ) := by omega
    unfold trunc0
    have hcast : ((2 : ℤ) ^ (Wd - 1)) = ((H : ℕ) : ℤ) := by push_cast [hH]; rfl
    rw [hcast]; simp only [hn, ↓reduceIte]
    congr 1
    have : ((e - H : ℕ) : ℤ) = (e : ℤ) - (H : ℕ) := by push_cast [Nat.cast_sub hc]; rfl
    rw [← this]
    push_cast
    rfl
  · have hlt : e < H := by omega
    set K := 2 ^ (Wd + 1 - s) with hK
    have hSK : 2 ^ s * K = 4 * H := by rw [hK, ← pow_add, ← h4]; congr 1; omega
    set q := (H - e) / 2 ^ s with hq
    set ρ := (H - e) % 2 ^ s with hρ
    have hdm : 2 ^ s * q + ρ = H - e := Nat.div_add_mod _ _
    have hρlt : ρ < 2 ^ s := Nat.mod_lt _ hs0
    have hqK : q < K := by
      by_contra hc'
      have : 2 ^ s * K ≤ 2 ^ s * q := Nat.mul_le_mul_left _ (by omega)
      omega
    have hd : digitVal Wd s e = 2 ^ s * (K - q) + (2 ^ s - 1 - ρ) := by
      have e1 : 2 ^ s * (K - q) = 2 ^ s * K - 2 ^ s * q := Nat.mul_sub _ _ _
      have e2 : 2 ^ s * q ≤ 2 ^ s * K := Nat.mul_le_mul_left _ hqK.le
      simp only [digitVal, ← hH, hc, ↓reduceIte]
      omega
    have hdiv : digitVal Wd s e / 2 ^ s = K - q := by
      rw [hd, Nat.mul_add_div hs0, Nat.div_eq_of_lt (by omega), add_zero]
    rw [hdiv]
    have hneg : ¬ (0 : ℤ) ≤ (e : ℤ) - 2 ^ (Wd - 1) := by
      have : ((2 : ℤ) ^ (Wd - 1)) = ((H : ℕ) : ℤ) := by push_cast [hH]; rfl
      rw [this]; omega
    unfold trunc0
    simp only [hneg, ↓reduceIte]
    have htq : (-((e : ℤ) - 2 ^ (Wd - 1))) / 2 ^ s = (q : ℤ) := by
      have : -((e : ℤ) - 2 ^ (Wd - 1)) = ((H - e : ℕ) : ℤ) := by
        rw [Nat.cast_sub hlt.le]; push_cast [hH]; ring
      rw [this, hq]; push_cast; rfl
    rw [htq]
    have hw : (2 : ℤ) ^ w ∣ (K : ℤ) := by
      rw [hK]; push_cast
      exact pow_dvd_pow 2 (by omega)
    obtain ⟨M, hM⟩ := hw
    rw [Nat.cast_sub hqK.le, hM]
    have : (2 : ℤ) ^ w * M - q = -(q : ℤ) + 2 ^ w * M := by ring
    rw [this, Int.add_mul_emod_self_left]

theorem digit_out {Wd s w e : ℕ} (hW : 1 ≤ Wd) (he : e < 2 ^ Wd) (hws : w + s ≤ Wd + 1) :
    (digitVal Wd s e / 2 ^ s) % 2 ^ w = ((trunc0 s ((e : ℤ) - 2 ^ (Wd - 1))) % 2 ^ w).toNat :=
  nat_mod_eq_toNat (digit_mod hW he hws)

theorem tw_digit {Wd s w e : ℕ} (hW : 1 ≤ Wd) (he : e < 2 ^ Wd) (hws : w + s ≤ Wd + 1) :
    bits w (digitVal Wd s e / 2 ^ s) = tw w (trunc0 s ((e : ℤ) - 2 ^ (Wd - 1))) := by
  rw [tw, ← digit_out hW he hws, bits_mod]

end IntegerMultBounds.Schoenhage
