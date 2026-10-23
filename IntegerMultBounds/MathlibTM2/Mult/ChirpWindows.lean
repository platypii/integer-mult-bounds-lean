module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpTableArgs

/-! # Geometry of overlapping chirp input windows

The cyclic extension covers indices from `-m` through `s+2m-1`. A block consumes
`3m+1` coefficients starting at its natural centre; successive centres advance at most
`m`. These facts justify a single forward sweep, with bounded overlapping copies.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds

def chirpCenter (s t m n : ℕ) : ℕ := s * (n * m) / t

@[simp] theorem chirpCenter_zero (s t m : ℕ) : chirpCenter s t m 0 = 0 := by
  simp [chirpCenter]

theorem chirpCenter_mono (s t m : ℕ) {n j : ℕ} (hnj : n ≤ j) :
    chirpCenter s t m n ≤ chirpCenter s t m j := by
  exact Nat.div_le_div_right (Nat.mul_le_mul_left s (Nat.mul_le_mul_right m hnj))

/-- A block step never skips more than `m` input records. -/
theorem chirpCenter_step {s t : ℕ} (hst : s ≤ t) (ht : 0 < t) (m n : ℕ) :
    chirpCenter s t m (n + 1) ≤ chirpCenter s t m n + m := by
  unfold chirpCenter
  calc s * ((n + 1) * m) / t = (s * (n * m) + s * m) / t := by congr 1; ring
    _ ≤ (s * (n * m) + t * m) / t :=
      Nat.div_le_div_right (Nat.add_le_add_left (Nat.mul_le_mul_right m hst) _)
    _ = s * (n * m) / t + m := Nat.add_mul_div_left _ _ ht

def chirpAdvance (s t m n : ℕ) : ℕ := chirpCenter s t m (n + 1) - chirpCenter s t m n

theorem chirpAdvance_le {s t : ℕ} (hst : s ≤ t) (ht : 0 < t) (m n : ℕ) :
    chirpAdvance s t m n ≤ m := by
  have := chirpCenter_step hst ht m n
  unfold chirpAdvance
  omega

theorem chirpCenter_add_advance (s t m n : ℕ) :
    chirpCenter s t m n + chirpAdvance s t m n = chirpCenter s t m (n + 1) := by
  have hmono : chirpCenter s t m n ≤ chirpCenter s t m (n + 1) :=
    chirpCenter_mono s t m (show n ≤ n + 1 by omega)
  unfold chirpAdvance
  omega

/-- The total forward sweep telescopes; it does not rescan the line per block. -/
theorem chirpAdvance_sum (s t m M : ℕ) :
    ((List.range M).map (chirpAdvance s t m)).sum = chirpCenter s t m M := by
  induction M with
  | zero => simp
  | succ M ih =>
    simpa only [List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, ih] using chirpCenter_add_advance s t m M

theorem chirpCenter_lt {s t m n : ℕ} (hs : 0 < s) (hn : n * m < t) :
    chirpCenter s t m n < s := by
  unfold chirpCenter
  apply Nat.div_lt_of_lt_mul
  simpa only [Nat.mul_comm t s] using Nat.mul_lt_mul_of_pos_left hn hs

/-- A finite cyclic extension; this definition imposes no artificial `m ≤ s` restriction. -/
def chirpExtended (s m : ℕ) (u : ZMod s → GaussianInt) : List GaussianInt :=
  (List.range (s + 3 * m)).map (fun x : ℕ => u (((x : ℤ) - m : ℤ) : ZMod s))

@[simp] theorem length_chirpExtended (s m : ℕ) (u : ZMod s → GaussianInt) :
    (chirpExtended s m u).length = s + 3 * m := by simp [chirpExtended]

def chirpWindow (s t m n : ℕ) (u : ZMod s → GaussianInt) : List GaussianInt :=
  ((chirpExtended s m u).drop (chirpCenter s t m n)).take (3 * m + 1)

theorem length_chirpWindow {s t m n : ℕ} (hs : 0 < s) (hn : n * m < t)
    (u : ZMod s → GaussianInt) : (chirpWindow s t m n u).length = 3 * m + 1 := by
  have := chirpCenter_lt hs hn
  simp only [chirpWindow, List.length_take, List.length_drop, length_chirpExtended]
  omega

/-- Window coefficients are precisely the cyclic input arguments of the analytic chirp. -/
theorem chirpWindow_getD {s t m n a : ℕ} (hs : 0 < s) (hn : n * m < t)
    (ha : a < 3 * m + 1) (u : ZMod s → GaussianInt) :
    (chirpWindow s t m n u).getD a 0 =
      u ((chirpStart s t m (n * m) + a : ℤ) : ZMod s) := by
  have hc := chirpCenter_lt hs hn
  have hlen : a < (chirpWindow s t m n u).length := by rw [length_chirpWindow hs hn]; exact ha
  rw [List.getD_eq_getElem _ _ hlen]
  simp only [chirpWindow, chirpExtended, List.getElem_take, List.getElem_drop,
    List.getElem_map, List.getElem_range]
  congr 1
  simp only [chirpStart, chirpCenter, Nat.cast_add]
  push_cast
  ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
