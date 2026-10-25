module

public import IntegerMultBounds.NLogN.ToeplitzDominant
import Mathlib.Data.List.GetD

/-! # Finite rounded iteration for Toeplitz inverse columns

The data constructor uses lists and field operations, so rational coefficients
and a computable rational rounding map give computable generator data. The
accuracy theorem compares those data with a specified solution. Tape execution,
coefficient generation and an iteration-count choice are separate obligations.
-/

@[expose] public section

namespace IntegerMultBounds.NLogN.ToeplitzInverse

open scoped BigOperators
open Finset

/-- Off-diagonal row evaluation, using structural list sums. -/
def generatorOffDiag {K : Type*} [Ring K] (g : ℕ → K) (x : List K) (i : ℕ) : K :=
  ((List.range x.length).map (fun k =>
    if k = i then 0 else g (gap i k) * x.getD k 0)).sum

/-- A rounded Jacobi step preserves the stored vector length. -/
def generatorStep {K : Type*} [Ring K] (g : ℕ → K) (rd : K → K)
    (b : ℕ → K) (x : List K) : List K :=
  (List.range x.length).map (fun i => rd (b i - generatorOffDiag g x i))

/-- Start with the zero vector and perform a finite number of rounded steps. -/
def generatorIter {K : Type*} [Ring K] (g : ℕ → K) (rd : K → K)
    (b : ℕ → K) (L : ℕ) : ℕ → List K
  | 0 => List.replicate L 0
  | n + 1 => generatorStep g rd b (generatorIter g rd b L n)

@[simp] theorem generatorStep_length {K : Type*} [Ring K] (g : ℕ → K)
    (rd : K → K) (b : ℕ → K) (x : List K) :
    (generatorStep g rd b x).length = x.length := by simp [generatorStep]

@[simp] theorem generatorIter_length {K : Type*} [Ring K] (g : ℕ → K)
    (rd : K → K) (b : ℕ → K) (L n : ℕ) :
    (generatorIter g rd b L n).length = L := by
  induction n with
  | zero => simp [generatorIter]
  | succ n hn => simpa only [generatorIter, generatorStep_length] using hn

private theorem sum_map_range {K : Type*} [AddCommMonoid K] (f : ℕ → K) (L : ℕ) :
    ((List.range L).map f).sum = ∑ k ∈ range L, f k := by
  induction L with
  | zero => simp
  | succ L h => simp [List.range_succ, h, sum_range_succ]

theorem generatorOffDiag_eq {K : Type*} [Ring K] (g : ℕ → K) (x : List K)
    (i : ℕ) (hi : i < x.length) :
    generatorOffDiag g x i = ∑ k ∈ (range x.length).erase i, g (gap i k) * x.getD k 0 := by
  unfold generatorOffDiag
  rw [sum_map_range]
  rw [← sum_erase_add _ _ (mem_range.mpr hi)]
  simp only [ite_true, add_zero]
  apply sum_congr rfl
  intro k hk
  simp only [if_neg (mem_erase.mp hk).1]

/-- Ring embeddings commute with the list evaluation, so rational data can
be interpreted in the real accuracy theorem without recomputing an inverse. -/
theorem generatorOffDiag_map {K F : Type*} [Ring K] [Ring F] (f : K →+* F)
    (g : ℕ → K) (x : List K) (i : ℕ) :
    generatorOffDiag (fun k => f (g k)) (x.map f) i = f (generatorOffDiag g x i) := by
  simp only [generatorOffDiag, List.length_map, sum_map_range, map_sum]
  apply sum_congr rfl
  intro k _
  by_cases hk : k = i
  · simp [hk]
  · simp only [if_neg hk, map_mul]
    congr 1
    simpa only [map_zero] using (List.getD_map (l := x) (d := (0 : K)) f (n := k))

/-- The unrounded rational recurrence embeds into the real recurrence. -/
theorem generatorIter_map {K F : Type*} [Ring K] [Ring F] (f : K →+* F)
    (g b : ℕ → K) (L n : ℕ) :
    (generatorIter g id b L n).map f =
      generatorIter (fun k => f (g k)) id (fun k => f (b k)) L n := by
  induction n with
  | zero => simp [generatorIter]
  | succ n hn =>
    simp only [generatorIter, generatorStep, List.map_map, List.length_map]
    rw [← hn]
    simp only [List.length_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, id_eq, map_sub, generatorOffDiag_map]

/-- A unit-diagonal solution is a fixed point of the unrounded step. -/
theorem generator_fixed_point {L : ℕ} {g b y : ℕ → ℝ} (hg : g 0 = 1)
    (hy : ∀ i < L, ∑ k ∈ range L, g (gap i k) * y k = b i)
    (i : ℕ) (hi : i < L) :
    b i - ∑ k ∈ (range L).erase i, g (gap i k) * y k = y i := by
  have h := hy i hi
  rw [← sum_erase_add _ _ (mem_range.mpr hi), gap_self, hg, one_mul] at h
  linarith

/-- The off-diagonal row mass is the contraction constant for one rounded step. -/
theorem generatorStep_error {L : ℕ} {g b y : ℕ → ℝ} {ρ δ ε : ℝ}
    (hg : g 0 = 1) (hρ : RowMass L g ρ)
    (rd : ℝ → ℝ) (hrd : ∀ z, |rd z - z| ≤ δ)
    (hy : ∀ i < L, ∑ k ∈ range L, g (gap i k) * y k = b i)
    (x : List ℝ) (hlen : x.length = L) (hε : 0 ≤ ε)
    (hx : ∀ k < L, |x.getD k 0 - y k| ≤ ε) (i : ℕ) (hi : i < L) :
    |(generatorStep g rd b x).getD i 0 - y i| ≤ δ + ρ * ε := by
  have hget : (generatorStep g rd b x).getD i 0 = rd (b i - generatorOffDiag g x i) := by
    simp [generatorStep, List.getD, hi, hlen]
  rw [hget]
  have hrow : |generatorOffDiag g x i - ∑ k ∈ (range L).erase i, g (gap i k) * y k| ≤ ρ * ε := by
    rw [generatorOffDiag_eq g x i (by omega), hlen, ← sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ (range L).erase i, |g (gap i k) * x.getD k 0 - g (gap i k) * y k| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ (range L).erase i, |g (gap i k)| * ε := by
        apply sum_le_sum
        intro k hk
        rw [← mul_sub, abs_mul]
        exact mul_le_mul_of_nonneg_left (hx k (mem_range.mp (mem_erase.mp hk).2)) (abs_nonneg _)
      _ = (∑ k ∈ (range L).erase i, |g (gap i k)|) * ε := (sum_mul _ _ _).symm
      _ ≤ ρ * ε := mul_le_mul_of_nonneg_right (hρ i hi) hε
  have hfix := generator_fixed_point hg hy i hi
  calc
    _ ≤ |rd (b i - generatorOffDiag g x i) - (b i - generatorOffDiag g x i)| +
        |(b i - generatorOffDiag g x i) - y i| := by
      simpa only [sub_add_sub_cancel] using abs_add_le
        (rd (b i - generatorOffDiag g x i) - (b i - generatorOffDiag g x i))
        ((b i - generatorOffDiag g x i) - y i)
    _ ≤ δ + ρ * ε := by
      apply add_le_add (hrd _)
      rw [show (b i - generatorOffDiag g x i) - y i =
        -(generatorOffDiag g x i - ∑ k ∈ (range L).erase i, g (gap i k) * y k) by linarith,
        abs_neg]
      exact hrow

/-- Rounding contributes a geometric error floor; the initial error contracts
at every finite step. No inverse is evaluated to construct the iterates. -/
theorem generatorIter_error {L : ℕ} {g b y : ℕ → ℝ} {ρ δ U : ℝ}
    (hg : g 0 = 1) (hρ : RowMass L g ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (rd : ℝ → ℝ) (hrd : ∀ z, |rd z - z| ≤ δ) (hδ : 0 ≤ δ) (hU : 0 ≤ U)
    (hy : ∀ i < L, ∑ k ∈ range L, g (gap i k) * y k = b i)
    (hyU : ∀ i < L, |y i| ≤ U) (n i : ℕ) (hi : i < L) :
    |(generatorIter g rd b L n).getD i 0 - y i| ≤ ρ ^ n * U + δ / (1 - ρ) := by
  induction n generalizing i with
  | zero =>
    have hz : (generatorIter g rd b L 0).getD i 0 = 0 := by
      simp [generatorIter, List.getD, hi]
    rw [hz, zero_sub, abs_neg, pow_zero, one_mul]
    exact (hyU i hi).trans (le_add_of_nonneg_right (div_nonneg hδ (by linarith)))
  | succ n hn =>
    have h := generatorStep_error hg hρ rd hrd hy (generatorIter g rd b L n)
      (generatorIter_length _ _ _ _ _) (by positivity : 0 ≤ ρ ^ n * U + δ / (1 - ρ))
      (fun k hk => hn k hk) i hi
    change |(generatorStep g rd b (generatorIter g rd b L n)).getD i 0 - y i| ≤ _
    convert h using 1
    rw [pow_succ]
    field_simp [show 1 - ρ ≠ 0 by linarith]
    <;> ring

/-- Specializing the finite iteration to a basis vector constructs an inverse
column. The exact inverse occurs only in the correctness statement. -/
theorem generatorIter_column_error {L : ℕ} {g : ℕ → ℝ} {ρ δ : ℝ}
    (hg : g 0 = 1) (hρ : RowMass L g ρ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (rd : ℝ → ℝ) (hrd : ∀ z, |rd z - z| ≤ δ) (hδ : 0 ≤ δ)
    (j : ℕ) (hj : j < L) (n i : ℕ) (hi : i < L) :
    |(generatorIter g rd (fun k => if k = j then 1 else 0) L n).getD i 0 - natInv L g i j| ≤
      ρ ^ n / (1 - ρ) + δ / (1 - ρ) := by
  have hU : 0 ≤ 1 / (1 - ρ) := by positivity
  have hbound : ∀ k < L, |natInv L g k j| ≤ 1 / (1 - ρ) := by
    intro k hk
    exact (single_le_sum (f := fun a => |natInv L g k a|) (fun _ _ => abs_nonneg _)
      (mem_range.mpr hj)).trans (row_abs_sum hg hρ hρ1 k hk)
  have h := generatorIter_error hg hρ hρ0 hρ1 rd hrd hδ hU
    (fun k hk => (isInverse hg hρ hρ1).right k j hk hj) hbound n i hi
  simpa only [mul_one_div] using h

/-- A computable rational inverse-column approximation, interpreted in `ℝ`.
This constructor needs no exact inverse or real rounding oracle. -/
theorem rationalGenerator_column_error {L : ℕ} (g : ℕ → ℚ) {ρ : ℝ}
    (hg : g 0 = 1) (hρ : RowMass L (fun k => (g k : ℝ)) ρ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (j : ℕ) (hj : j < L) (n i : ℕ) (hi : i < L) :
    |((generatorIter g id (fun k => if k = j then 1 else 0) L n).getD i 0 : ℝ) -
      natInv L (fun k => (g k : ℝ)) i j| ≤ ρ ^ n / (1 - ρ) := by
  have hmap := generatorIter_map (Rat.castHom ℝ) g (fun k => if k = j then 1 else 0) L n
  have hget := congrArg (fun x : List ℝ => x.getD i 0) hmap
  rw [show (0 : ℝ) = (Rat.castHom ℝ) 0 from (map_zero _).symm, List.getD_map] at hget
  have h := generatorIter_column_error (g := fun k => (g k : ℝ)) (δ := 0)
    (by simp [hg]) hρ hρ0 hρ1 id (by simp) (by norm_num) j hj n i hi
  have hget' : ((generatorIter g id (fun k => if k = j then 1 else 0) L n).getD i 0 : ℝ) =
      (generatorIter (fun k => (g k : ℝ)) id (fun k => if k = j then 1 else 0) L n).getD i 0 := by
    simpa only [apply_ite, map_one, map_zero, Rat.coe_castHom] using hget
  rw [← hget'] at h
  simpa only [zero_div, add_zero] using h

end IntegerMultBounds.NLogN.ToeplitzInverse
