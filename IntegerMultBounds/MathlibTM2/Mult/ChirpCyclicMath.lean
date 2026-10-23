module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpRepeat
public import IntegerMultBounds.MathlibTM2.Mult.ChirpWindows
public import Mathlib.Data.List.Rotate

/-! # A rotated repeated line is the chirp cyclic extension

Choose enough whole periods to cover the extension. The overshoot is shorter than one
period, including when the window radius is larger than the original line.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds

def chirpOffset (s m : ℕ) : ℕ := (s - m % s) % s

def chirpPeriods (s m : ℕ) : ℕ := (s + 3 * m - 1) / s + 1

def chirpLine (s : ℕ) (u : ZMod s → GaussianInt) : List GaussianInt :=
  (List.range s).map (fun i : ℕ => u (i : ZMod s))

@[simp] theorem length_chirpLine (s : ℕ) (u : ZMod s → GaussianInt) :
    (chirpLine s u).length = s := by simp [chirpLine]

theorem chirpOffset_lt {s : ℕ} (hs : 0 < s) (m : ℕ) : chirpOffset s m < s := Nat.mod_lt _ hs

theorem chirpPeriods_cover {s : ℕ} (hs : 0 < s) (m : ℕ) :
    s + 3 * m ≤ chirpPeriods s m * s := by
  have hdiv : ((s + 3 * m - 1) / s) * s + (s + 3 * m - 1) % s = s + 3 * m - 1 := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod (s + 3 * m - 1) s
  have hmod := Nat.mod_lt (s + 3 * m - 1) hs
  unfold chirpPeriods
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem chirpPeriods_overshoot {s : ℕ} (hs : 0 < s) (m : ℕ) :
    chirpPeriods s m * s < (s + 3 * m) + s := by
  unfold chirpPeriods
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.add_lt_add_right ((Nat.div_mul_le_self _ _).trans_lt
    (Nat.sub_lt (by omega) (by decide))) _

/-- Modular source index of a whole-period repetition. -/
theorem repeatStream_getElem? {α : Type} (C : ℕ) (xs : List α) (i : ℕ)
    (hi : i < C * xs.length) : (repeatStream C xs)[i]? = xs[i % xs.length]? := by
  induction C generalizing i with
  | zero => simp at hi
  | succ C ih =>
    have he : repeatStream (C + 1) xs = xs ++ repeatStream C xs := by
      simp [repeatStream, List.replicate_succ]
    rw [he]
    by_cases hx : i < xs.length
    · rw [List.getElem?_append_left hx, Nat.mod_eq_of_lt hx]
    · have hx : xs.length ≤ i := by omega
      rw [List.getElem?_append_right hx, ih (i - xs.length) (by rw [Nat.succ_mul] at hi; omega)]
      congr 1
      conv_rhs => rw [← Nat.sub_add_cancel hx]
      rw [Nat.add_mod_right]

/-- Cast away a complete number of periods without assuming a nonzero modulus instance. -/
theorem chirpMod_cast (s i : ℕ) : ((i % s : ℕ) : ZMod s) = (i : ZMod s) := by
  have h := congrArg (fun n : ℕ => (n : ZMod s)) (Nat.mod_add_div i s)
  simpa only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] using h

theorem chirpOffset_cast {s : ℕ} (hs : 0 < s) (m : ℕ) :
    (chirpOffset s m : ZMod s) = -(m : ZMod s) := by
  unfold chirpOffset
  rw [chirpMod_cast, Nat.cast_sub (Nat.mod_lt m hs).le, ZMod.natCast_self, chirpMod_cast, zero_sub]

/-- Repeating the rotated raw line and taking the required length gives the exact extension. -/
theorem chirpExtended_eq_repeat {s : ℕ} (hs : 0 < s) (m : ℕ) (u : ZMod s → GaussianInt) :
    (repeatStream (chirpPeriods s m) ((chirpLine s u).rotate (chirpOffset s m))).take (s + 3 * m) =
      chirpExtended s m u := by
  have hcover := chirpPeriods_cover hs m
  apply List.ext_getElem
  · simp only [List.length_take, length_repeatStream, List.length_rotate, length_chirpLine,
      Nat.min_eq_left hcover, length_chirpExtended]
  intro i hi hi'
  have hib : i < s + 3 * m := by simpa using hi'
  have hip : i < chirpPeriods s m * ((chirpLine s u).rotate (chirpOffset s m)).length := by
    simpa using hib.trans_le hcover
  have hlookup := repeatStream_getElem? (chirpPeriods s m)
    ((chirpLine s u).rotate (chirpOffset s m)) i hip
  have hperiod : 0 < ((chirpLine s u).rotate (chirpOffset s m)).length := by simpa using hs
  have himod := Nat.mod_lt i hperiod
  rw [List.getElem?_eq_getElem (by simpa using hip), List.getElem?_eq_getElem himod] at hlookup
  simp only [List.getElem_take]
  rw [Option.some.inj hlookup, List.getElem_rotate]
  simp only [chirpLine, chirpExtended, List.getElem_map, List.getElem_range, List.length_rotate,
    List.length_map, List.length_range]
  congr 1
  rw [chirpMod_cast, Nat.cast_add, chirpMod_cast, chirpOffset_cast hs]
  simp only [Int.cast_sub, Int.cast_natCast]
  simp only [sub_eq_add_neg]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
