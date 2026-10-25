module

public import IntegerMultBounds.NLogN.ToeplitzGeneratorIteration
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.List.GetD

/-! # Integer numerators for the dyadic inverse-column recurrence

Each iteration uses only integer additions and products. Dividing the n-th
stored vector by 2^(P*n) recovers the existing exact rational recurrence.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.ToeplitzInverse

theorem generatorOffDiag_scale {K : Type*} [Field K] (a b : K) (g : ℕ → K) (x : List K) (i : ℕ) :
    generatorOffDiag (fun k => a * g k) (x.map (fun z => b * z)) i = a * b * generatorOffDiag g x i := by
  have hget (k : ℕ) : (x.map (fun z => b * z)).getD k 0 = b * x.getD k 0 := by
    simpa only [mul_zero] using List.getD_map (l := x) (d := (0 : K)) (fun z => b * z) (n := k)
  unfold generatorOffDiag
  simp only [List.length_map]
  calc
    _ = ((List.range x.length).map (fun k => a * b * (if k = i then 0 else g (gap i k) * x.getD k 0))).sum := by
      congr 1
      apply List.map_congr_left
      intro k _
      rw [hget]
      split_ifs <;> ring
    _ = _ := List.sum_map_mul_left _ _ _

theorem generatorOffDiag_div {K : Type*} [Field K] (D E : K) (g : ℕ → K) (x : List K) (i : ℕ) :
    generatorOffDiag (fun k => g k / D) (x.map (fun z => z / E)) i = generatorOffDiag g x i / (D * E) := by
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using generatorOffDiag_scale D⁻¹ E⁻¹ g x i

theorem generatorOffDiag_int_div (D E : ℚ) (c : ℕ → ℤ) (x : List ℤ) (i : ℕ) :
    generatorOffDiag (fun k => (c k : ℚ) / D) (x.map (fun z : ℤ => (z : ℚ) / E)) i =
      ((generatorOffDiag c x i : ℤ) : ℚ) / (D * E) := by
  let f : ℤ →+* ℚ := Int.castRingHom ℚ
  have hmap : x.map (fun z : ℤ => (z : ℚ) / E) = (x.map f).map (fun z => z / E) := by
    rw [List.map_map]
    rfl
  rw [hmap, generatorOffDiag_div]
  congr 1
  exact generatorOffDiag_map f c x i

/-- The n-th vector stores integer numerators at denominator 2^(P*n). -/
def dyadicGeneratorIter (P : ℕ) (c b : ℕ → ℤ) (L : ℕ) : ℕ → List ℤ
  | 0 => List.replicate L 0
  | n + 1 => generatorStep c id (fun i => (2 : ℤ) ^ (P * (n + 1)) * b i)
      (dyadicGeneratorIter P c b L n)

@[simp] theorem dyadicGeneratorIter_length (P : ℕ) (c b : ℕ → ℤ) (L n : ℕ) :
    (dyadicGeneratorIter P c b L n).length = L := by
  induction n with
  | zero => simp [dyadicGeneratorIter]
  | succ n ih => simpa only [dyadicGeneratorIter, generatorStep_length] using ih

/-- The integer recurrence computes the exact rational data, without intermediate
rational reductions or an inverse-column oracle. -/
theorem dyadicGeneratorIter_spec (P : ℕ) (c b : ℕ → ℤ) (L n : ℕ) :
    (dyadicGeneratorIter P c b L n).map (fun z : ℤ => (z : ℚ) / (2 : ℚ) ^ (P * n)) =
      generatorIter (fun k => (c k : ℚ) / (2 : ℚ) ^ P) id (fun k => (b k : ℚ)) L n := by
  induction n with
  | zero => simp [dyadicGeneratorIter, generatorIter]
  | succ n ih =>
      rw [generatorIter, ← ih]
      simp only [dyadicGeneratorIter, generatorStep, List.map_map, List.length_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, id_eq, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      rw [generatorOffDiag_int_div]
      have hpow : (2 : ℚ) ^ (P * (n + 1)) = (2 : ℚ) ^ P * (2 : ℚ) ^ (P * n) := by
        rw [← pow_add]
        congr 1
        ring
      rw [hpow]
      field_simp

end IntegerMultBounds.NLogN.ToeplitzInverse
