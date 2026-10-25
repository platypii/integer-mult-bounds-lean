module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvPacking
public import IntegerMultBounds.NLogN.PhaseCellIntegerGenerators

/-! # Symbol format of the integer generator's scaled-unit seed -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

theorem csyms_power_two (A W P : ℕ) (hP : P < W) :
    csyms A W (⟨(2 : ℤ) ^ P, 0⟩ : GaussianInt) =
      List.replicate P (pairSym A false false) ++ pairSym A true false ::
        List.replicate (W - P - 1) (pairSym A false false) := by
  have hpow : (2 : ℕ) ^ P < 2 ^ W := Nat.pow_lt_pow_right (by decide) hP
  have hval : ((2 : ZMod (2 ^ W)) ^ P).val = (2 : ℕ) ^ P := by
    have hh := ZMod.val_natCast_of_lt hpow
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Int.cast_pow, Int.cast_ofNat] using hh
  apply List.ext_getElem (by simp; omega)
  intro i hi hj
  simp only [csyms, coeffSyms, red, List.getElem_ofFn, Int.cast_pow, Int.cast_ofNat, hval, Int.cast_zero,
    ZMod.val_zero, Nat.zero_testBit, Nat.testBit_two_pow]
  by_cases hip : i < P
  · rw [List.getElem_append_left (by simpa using hip), List.getElem_replicate]
    simp [show P ≠ i by omega]
  · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hip)]
    by_cases hie : i = P
    · subst i; simp
    · simp only [List.length_replicate]
      rw [List.getElem_cons]
      simp [show i - P ≠ 0 by omega, show P ≠ i by omega]

def seedWords (P L : ℕ) : List GaussianInt :=
  (List.range L).map (fun i => (⟨if i = 0 then (2 : ℤ) ^ P else 0, 0⟩ : GaussianInt))

theorem seedWords_succ (P L : ℕ) : seedWords P (L + 1) =
    (⟨(2 : ℤ) ^ P, 0⟩ : GaussianInt) :: List.replicate L 0 := by
  simp only [seedWords, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  trans List.map (fun _ : ℕ => (0 : GaussianInt)) (List.range L)
  · apply List.map_congr_left
    intro i _
    rfl
  · simp

theorem seedWords_eq_column (P s t u band L : ℕ) :
    seedWords P L = List.map (fun z : ℤ => (⟨z, 0⟩ : GaussianInt))
      (IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.columnNumerators P s t u band L 1) := by
  rw [IntegerMultBounds.NLogN.PhaseCellIntegerGenerators.columnNumerators_one, List.map_map]
  rfl

private theorem zeroStream (A W L : ℕ) :
    cstream A W (List.replicate L 0) = List.replicate (L * W) (pairSym A false false) := by
  induction L with
  | zero => simp [cstream]
  | succ L ih =>
      rw [List.replicate_succ, cstream_cons, csyms_zero, ih, List.replicate_append_replicate]
      congr 1
      ring

/-- Descending generator rows need zero words followed by the scaled unit. -/
theorem reversedSeedStream (A W P L : ℕ) (hL : 0 < L) :
    cstream A W ((seedWords P L).reverse) =
      List.replicate ((L - 1) * W) (pairSym A false false) ++
        csyms A W (⟨(2 : ℤ) ^ P, 0⟩ : GaussianInt) := by
  cases L with
  | zero => omega
  | succ L =>
    rw [seedWords_succ, List.reverse_cons, List.reverse_replicate, cstream_append, zeroStream]
    simp

/-- Seed emission is just a zero prefix with its P-th symbol replaced. -/
theorem seedStream (A W P L : ℕ) (hP : P < W) (hL : 0 < L) :
    cstream A W (seedWords P L) =
      List.replicate P (pairSym A false false) ++ pairSym A true false ::
        List.replicate (L * W - P - 1) (pairSym A false false) := by
  cases L with
  | zero => omega
  | succ L =>
      rw [seedWords_succ, cstream_cons, csyms_power_two A W P hP, zeroStream]
      simp only [List.append_assoc, List.cons_append, List.replicate_append_replicate]
      have hh : W - P - 1 + L * W = (L + 1) * W - P - 1 := by rw [Nat.succ_mul]; omega
      rw [hh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
