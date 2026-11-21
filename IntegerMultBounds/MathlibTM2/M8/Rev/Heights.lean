module

public import IntegerMultBounds.MathlibTM2.M8.Rev.Edge
public import IntegerMultBounds.MathlibTM2.M8.ExchangeBound
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Heights of the stage-2 edge programs

The stage-2 program of `U` is the stage-1 exchange program of the factorization of `U C`, with
`C` the reversal of the coordinates. Multiplying by `C` permutes columns, so it keeps every
height (`bounded_mul_rev`). Hence the numbers and coefficients of `revProgram U` are bounded by
the stage-1 exponent of `U C` (`revNumbers_le`, `revProgram_coeffs_le`), and for size at most
`529` that exponent is at most `2 ^ 53000` once the entries of `U C` have heights at most
`2 ^ (2 ^ 36)` (`numbersE_le_of_exp`), far below `Networks.coefficientBound`.

A basis with natural entries at most `2 ^ e` has an inverse with heights at most
`2 ^ (2 m (k + e))` for `m ≤ 2 ^ k` (`bounded_inv_natCast`): the inverse is the adjugate over the
determinant, both integers bounded by `m! (2 ^ e) ^ m` (`Matrix.det_le`).
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Rev

noncomputable section
open Matrix Finset
open IntegerMultBounds.Networks
open IntegerMultBounds.Swap.Shear (pivotMatrix)
open IntegerMultBounds.Swap.Modular (denominators)
open Exchange (expOf facE numbersE opCoeffs factors_bounded bounded_expOf den_mem_le bounded_map_inv
  bounded_pivot transformOps_coeffs crossQ_coeffs exchangeOps)
open ReversedExchange (rev)
open Height (ht Bounded)

variable {m : ℕ}

/-! ### Reversal keeps heights -/

theorem mul_rev_apply (A : Matrix (Fin m) (Fin m) ℚ) (i j : Fin m) :
    (A * (rev m : Matrix (Fin m) (Fin m) ℚ)) i j = A i j.rev := by
  rw [mul_apply, Finset.sum_eq_single j.rev]
  · simp [rev]
  · intro k _ hk
    have : ¬ j = k.rev := fun h => hk (by rw [h, Fin.rev_rev])
    simp [rev, this]
  · simp

theorem bounded_mul_rev {A : Matrix (Fin m) (Fin m) ℚ} {h : ℕ} (hA : Bounded A h) :
    Bounded (A * rev m) h := fun i j => by rw [mul_rev_apply]; exact hA _ _

theorem bounded_rev : Bounded (rev m : Matrix (Fin m) (Fin m) ℚ) (2 ^ 0) := fun i j => by
  simp only [rev, of_apply]
  split_ifs <;> simp [Height.ht]

/-- The bit length bound of a bounded matrix. -/
theorem expOf_le {A : Matrix (Fin m) (Fin m) ℚ} {e : ℕ} (hA : Bounded A (2 ^ e)) : expOf A ≤ e + 1 := by
  unfold expOf
  rw [Nat.size_le]
  exact lt_of_le_of_lt (Finset.sup_le fun p _ => hA p.1 p.2) (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-! ### Numbers and coefficients -/

local notation "N" => Fintype.card (Fin m)

theorem bounded_revCorr (U : Matrix (Fin m) (Fin m) ℚ) (hN : 1 ≤ N) :
    Bounded (revCorr U) (2 ^ (14 * N ^ 3 * (facE (U * rev m) + 1))) := by
  obtain ⟨h₁, _, h₂, _⟩ := factors_bounded (U * rev m)
  have hP := bounded_pivot (revFactors U).L ((revFactors U).nodup₁.of_map _)
  have hPt := Height.bounded_transpose hP
  have hM := Height.bounded_mul (bounded_mul_rev h₂) h₁
  have hPPt := Height.bounded_mul hP hPt
  have hPtP := Height.bounded_mul hPt hP
  have t1 := Height.bounded_mul hM hPPt
  have t2 := Height.bounded_mul hPtP hM
  have t3 := Height.bounded_mul t2 hPPt
  have k := Height.bounded_sub (Height.bounded_add (Height.bounded_sub t1 t2) t3) hPt
  refine k.pow_mono ?_
  change _ ≤ 14 * N ^ 3 * (Height.FE N (2 * N) (expOf (U * rev m)) + 1)
  set e := Height.FE N (2 * N) (expOf (U * rev m))
  have hN2 : N ≤ N ^ 2 := by nlinarith
  have hN3 : N ^ 2 ≤ N ^ 3 := by nlinarith
  nlinarith [Nat.zero_le e, Nat.zero_le (N * e), Nat.zero_le (N ^ 2 * e)]

/-- **Bounded numbers** of the stage-2 program. -/
theorem revNumbers_le (U : Matrix (Fin m) (Fin m) ℚ) (hN : 1 ≤ N) :
    ∀ d ∈ revNumbers U, d ≤ 2 ^ numbersE (U * rev m) := by
  obtain ⟨h₁, h₁', h₂, h₂'⟩ := factors_bounded (U * rev m)
  have hf : facE (U * rev m) ≤ numbersE (U * rev m) := Exchange.facE_le_numbersE _
  have hK := bounded_revCorr U hN
  have hk : 14 * N ^ 3 * (facE (U * rev m) + 1) ≤ numbersE (U * rev m) := Exchange.corrE_le_numbersE _
  have hU : expOf (U * rev m) ≤ numbersE (U * rev m) := le_max_left _ _
  have hUb : Bounded U (2 ^ expOf (U * rev m)) := by
    have := bounded_mul_rev (bounded_expOf (U * rev m))
    rwa [Matrix.mul_assoc, ReversedExchange.rev_mul_rev, Matrix.mul_one] at this
  intro d hd
  simp only [revNumbers, Swap.Modular.factorizationDenominators, Finset.mem_union] at hd
  rcases hd with ((((((((((hd | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd) | hd)
  · exact den_mem_le (bounded_expOf (U * rev m)) hU hd
  · exact den_mem_le h₁ hf hd
  · exact den_mem_le h₁' hf hd
  · exact den_mem_le h₂ hf hd
  · exact den_mem_le h₂' hf hd
  · exact den_mem_le hK hk hd
  · exact den_mem_le (bounded_map_inv hK) hk hd
  · exact den_mem_le (Height.bounded_neg hK) hk hd
  · exact den_mem_le (bounded_map_inv (Height.bounded_neg hK)) hk hd
  · exact den_mem_le hUb hU hd
  · exact den_mem_le bounded_rev (Nat.zero_le _) hd

/-- Every coefficient of the stage-2 program has height at most `2 ^ numbersE (U C)`. -/
theorem revProgram_coeffs_le (U : Matrix (Fin m) (Fin m) ℚ) (hN : 1 ≤ N) :
    ∀ op ∈ revProgram U, ∀ r ∈ opCoeffs op, ht r ≤ 2 ^ numbersE (U * rev m) := by
  obtain ⟨h₁, h₁', h₂, h₂'⟩ := factors_bounded (U * rev m)
  have hf : facE (U * rev m) ≤ numbersE (U * rev m) := Exchange.facE_le_numbersE _
  have hK := (bounded_revCorr U hN).pow_mono (Exchange.corrE_le_numbersE _)
  have h1 : 1 ≤ 2 ^ numbersE (U * rev m) := Nat.one_le_two_pow
  intro op hop r hr
  simp only [revProgram, exchangeOps, List.mem_append] at hop
  rcases hop with (((h | h) | h) | h) | h
  · exact transformOps_coeffs (h₁'.pow_mono hf) (h₂.pow_mono hf) op h r hr
  · exact crossQ_coeffs hK h1 op h r hr
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
    simp [opCoeffs] at hr
  · exact crossQ_coeffs (Height.bounded_neg hK) h1 op h r hr
  · exact transformOps_coeffs (h₁.pow_mono hf) (h₂'.pow_mono hf) op h r hr

/-- For size at most `529` and entry heights at most `2 ^ (2 ^ 36)`, the exponent is at most
`2 ^ 53000`. -/
theorem numbersE_le_of_exp (V : Matrix (Fin m) (Fin m) ℚ) (hN : 1 ≤ N) (hN' : N ≤ 529)
    (hexp : expOf V ≤ 2 ^ 36) : numbersE V ≤ 2 ^ 53000 := by
  have hbase : 16 * N ^ 5 ≤ 2 ^ 50 :=
    (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hN' 5)).trans (by norm_num)
  have hpow : (16 * N ^ 5) ^ (2 * N) ≤ 2 ^ 52900 := by
    calc (16 * N ^ 5) ^ (2 * N) ≤ (2 ^ 50) ^ (2 * N) := Nat.pow_le_pow_left hbase _
      _ ≤ (2 ^ 50) ^ 1058 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 2 ^ 52900 := (pow_mul 2 50 1058).symm.trans (congrArg (fun k => 2 ^ k) (by norm_num))
  have hfac : facE V ≤ 2 ^ 52937 := by
    calc facE V ≤ (16 * N ^ 5) ^ (2 * N) * (expOf V + 1) := Height.FE_le N hN _ _
      _ ≤ 2 ^ 52900 * 2 ^ 37 := Nat.mul_le_mul hpow (by
          have : (2 : ℕ) ^ 36 + 1 ≤ 2 ^ 37 := by norm_num
          omega)
      _ = 2 ^ 52937 := by rw [← pow_add]
  have hN3 : 14 * N ^ 3 ≤ 2 ^ 32 :=
    (Nat.mul_le_mul_left 14 (Nat.pow_le_pow_left hN' 3)).trans (by norm_num)
  have hk : 14 * N ^ 3 * (facE V + 1) ≤ 2 ^ 53000 := by
    calc 14 * N ^ 3 * (facE V + 1) ≤ 2 ^ 32 * (2 ^ 52937 + 2 ^ 52937) :=
          Nat.mul_le_mul hN3 (by have := Nat.one_le_two_pow (n := 52937); omega)
      _ = 2 ^ 52970 := by rw [← two_mul, ← pow_succ', ← pow_add]
      _ ≤ 2 ^ 53000 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  refine max_le (hexp.trans ?_) (max_le (hfac.trans ?_) hk)
  · exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  · exact pow_le_pow_right₀ (by norm_num) (by norm_num)

/-- The numbers of the stage-2 program are at most `coefficientBound`. -/
theorem revNumbers_le_coefficientBound (U : Matrix (Fin m) (Fin m) ℚ) (hN : 1 ≤ N) (hN' : N ≤ 529)
    (hexp : expOf (U * rev m) ≤ 2 ^ 36) : ∀ d ∈ revNumbers U, d ≤ coefficientBound := fun d hd =>
  (revNumbers_le U hN d hd).trans (Exchange.le_coefficientBound (numbersE_le_of_exp _ hN hN' hexp))

/-- The coefficients of the stage-2 program are at most `coefficientBound`. -/
theorem revProgram_coeffs_le_coefficientBound (U : Matrix (Fin m) (Fin m) ℚ) (hN : 1 ≤ N)
    (hN' : N ≤ 529) (hexp : expOf (U * rev m) ≤ 2 ^ 36) :
    ∀ op ∈ revProgram U, ∀ r ∈ opCoeffs op,
      r.num.natAbs ≤ coefficientBound ∧ r.den ≤ coefficientBound := by
  intro op hop r hr
  have h := (revProgram_coeffs_le U hN op hop r hr).trans
    (Exchange.le_coefficientBound (numbersE_le_of_exp _ hN hN' hexp))
  exact ⟨(Height.num_le_ht r).trans h, (Height.den_le_ht r).trans h⟩

/-! ### The inverse of a natural basis -/

theorem ht_intCast (n : ℤ) : ht (n : ℚ) = max n.natAbs 1 := by
  simp [Height.ht]

theorem natAbs_det_le {A : Matrix (Fin m) (Fin m) ℤ} {x : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ x) :
    A.det.natAbs ≤ m.factorial * x ^ m := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (x := (x : ℤ)) fun i j => by
    rw [AbsoluteValue.abs_apply, Int.abs_eq_natAbs]; exact_mod_cast hA i j
  rw [AbsoluteValue.abs_apply, Int.abs_eq_natAbs, Fintype.card_fin, nsmul_eq_mul] at h
  exact_mod_cast h

/-- Determinant and adjugate bounds for an integral change of coordinates. -/
theorem bounded_inv_intCast {gZ : Matrix (Fin m) (Fin m) ℤ} {e k : ℕ}
    (hg : ∀ a b, (gZ a b).natAbs ≤ 2 ^ e) (hm : m ≤ 2 ^ k) :
    Bounded (gZ.map (Int.castRingHom ℚ))⁻¹ (2 ^ (2 * (m * (k + e)))) := by
  have hb : m.factorial * (2 ^ e) ^ m ≤ 2 ^ (m * (k + e)) := by
    calc m.factorial * (2 ^ e) ^ m ≤ m ^ m * (2 ^ e) ^ m := Nat.mul_le_mul_right _ (Nat.factorial_le_pow m)
      _ ≤ (2 ^ k) ^ m * (2 ^ e) ^ m := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hm m)
      _ = 2 ^ (m * (k + e)) := by rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  have hone : 1 ≤ 2 ^ (m * (k + e)) := Nat.one_le_two_pow
  have hdet : gZ.det.natAbs ≤ 2 ^ (m * (k + e)) :=
    (natAbs_det_le hg).trans hb
  have hadj : ∀ i j, (gZ.adjugate i j).natAbs ≤ 2 ^ (m * (k + e)) := by
    intro i j
    rw [adjugate_apply]
    refine (natAbs_det_le (x := 2 ^ e) fun a c => ?_).trans hb
    by_cases ha : a = j
    · subst ha
      rw [updateRow_self]
      by_cases hc : c = i
      · subst hc; simp [Nat.one_le_two_pow]
      · simp [hc]
    · rw [updateRow_ne ha]; exact hg a c
  have hdetQ : (gZ.map (Int.castRingHom ℚ)).det = ((gZ.det : ℤ) : ℚ) := by
    rw [← eq_intCast (Int.castRingHom ℚ), RingHom.map_det]; rfl
  have hadjQ : (gZ.map (Int.castRingHom ℚ)).adjugate = gZ.adjugate.map (Int.castRingHom ℚ) :=
    (RingHom.map_adjugate (Int.castRingHom ℚ) gZ).symm
  intro i j
  rw [Matrix.inv_def, hdetQ, hadjQ, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv', map_apply]
  refine (Height.ht_mul _ _).trans ?_
  rw [Height.ht_inv, eq_intCast, ht_intCast, ht_intCast, two_mul, pow_add]
  exact Nat.mul_le_mul (max_le hdet hone) (max_le (hadj i j) hone)

theorem bounded_inv_natCast {g : Matrix (Fin m) (Fin m) ℕ} {e k : ℕ} (hg : ∀ a b, g a b ≤ 2 ^ e)
    (hm : m ≤ 2 ^ k) : Bounded (g.map (Nat.cast : ℕ → ℚ))⁻¹ (2 ^ (2 * (m * (k + e)))) := by
  let gZ := g.map (Nat.cast : ℕ → ℤ)
  have eq : g.map (Nat.cast : ℕ → ℚ) = gZ.map (Int.castRingHom ℚ) := by ext; simp [gZ]
  rw [eq]
  exact bounded_inv_intCast (fun i j => by simpa [gZ] using hg i j) hm

/-- A natural basis is bounded. -/
theorem bounded_natCast {g : Matrix (Fin m) (Fin m) ℕ} {e : ℕ} (hg : ∀ a b, g a b ≤ 2 ^ e) :
    Bounded (g.map (Nat.cast : ℕ → ℚ)) (2 ^ e) := fun a b => by
  simp only [map_apply, Height.ht, Rat.num_natCast, Rat.den_natCast, Int.natAbs_natCast]
  exact max_le (hg a b) Nat.one_le_two_pow

end

end IntegerMultBounds.MathlibTM2.M8.Rev
