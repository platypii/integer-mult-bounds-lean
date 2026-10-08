import IntegerMultBounds.NLogN.DFT
import IntegerMultBounds.NLogN.FFT
import Mathlib.RingTheory.AdjoinRoot

/-! Principal roots of unity and the synthetic coefficient ring `ℂ[y]/(y^r + 1)`.
A principal root satisfies the vanishing character sums directly, so transform
inversion goes through over any commutative ring, in particular over the
synthetic ring, which is not a domain. Proved: primitive roots of domains are
principal, the inverse power of a principal root is principal, orthogonality
and double-transform inversion from the principal property alone, `y^r = -1`
in the synthetic ring, `y^(2r/t)` is a principal `t`-th root for every power
of two `t ∣ 2r`, and hence the radix-2 recursion computes the synthetic
transform exactly. The coefficient-norm bound `‖ab‖ ≤ r ‖a‖ ‖b‖`, precision,
and costs are not here. -/

namespace IntegerMultBounds.NLogN

variable {S : Type*} [CommRing S] {N : ℕ} {ζ : S}

/-- `ζ ^ N = 1` and every nontrivial character sum vanishes. -/
def IsPrincipalRoot (ζ : S) (N : ℕ) : Prop :=
  ζ ^ N = 1 ∧ ∀ m : ℕ, 0 < m → m < N → ∑ j ∈ Finset.range N, ζ ^ (j * m) = 0

theorem isPrincipalRoot_of_isPrimitiveRoot [IsDomain S] (hζ : IsPrimitiveRoot ζ N) :
    IsPrincipalRoot ζ N := by
  refine ⟨hζ.pow_eq_one, fun m hm hmN => ?_⟩
  have hx : ζ ^ m ≠ 1 := by
    intro h1
    rw [hζ.pow_eq_one_iff_dvd] at h1
    exact absurd (Nat.eq_zero_of_dvd_of_lt h1 hmN) (by omega)
  have hN : (ζ ^ m) ^ N = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hmul := geom_sum_mul (ζ ^ m) N
  rw [hN, sub_self, mul_eq_zero] at hmul
  simp_rw [mul_comm _ m, pow_mul]
  exact hmul.resolve_right (sub_ne_zero.2 hx)

theorem pow_eq_pow_of_modEq (hζ : ζ ^ N = 1) {a b : ℕ} (h : a ≡ b [MOD N]) :
    ζ ^ a = ζ ^ b := by
  rw [pow_mod_eq hζ a, pow_mod_eq hζ b, h]

/-- The inverse `ζ⁻¹ = ζ^(N-1)` of a principal root is principal. -/
theorem IsPrincipalRoot.inv_pow (h : IsPrincipalRoot ζ N) :
    IsPrincipalRoot (ζ ^ (N - 1)) N := by
  obtain ⟨hN, hsum⟩ := h
  refine ⟨by rw [← pow_mul, mul_comm, pow_mul, hN, one_pow], fun m hm hmN => ?_⟩
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  have key : ∀ j : ℕ, (ζ ^ (N' + 1 - 1)) ^ (j * m) = ζ ^ (j * (N' + 1 - m)) := by
    intro j
    rw [← pow_mul]
    apply pow_eq_pow_of_modEq hN
    have e1 : (N' + 1 - 1) * (j * m) + j * m = (N' + 1) * (j * m) := by
      simp only [Nat.add_sub_cancel]; ring
    have e2 : j * (N' + 1 - m) + j * m = (N' + 1) * j := by
      rw [← mul_add, Nat.sub_add_cancel (by omega)]; ring
    refine Nat.ModEq.add_right_cancel' (j * m) ?_
    rw [e1, e2]
    exact (Nat.modEq_zero_iff_dvd.2 (dvd_mul_right _ _)).trans
      (Nat.modEq_zero_iff_dvd.2 (dvd_mul_right _ _)).symm
  simp_rw [key]
  exact hsum (N' + 1 - m) (by omega) (by omega)

section ZMod

variable [NeZero N]

omit [NeZero N] in
theorem pow_val_natCast' (hζ : ζ ^ N = 1) (n : ℕ) :
    ζ ^ ((n : ZMod N)).val = ζ ^ n := by
  rw [ZMod.val_natCast]
  exact (pow_mod_eq hζ n).symm

theorem pow_val_add' (hζ : ζ ^ N = 1) (x y : ZMod N) :
    ζ ^ (x + y).val = ζ ^ x.val * ζ ^ y.val := by
  have h : x + y = ((x.val + y.val : ℕ) : ZMod N) := by push_cast; simp
  rw [h, pow_val_natCast' hζ, pow_add]

theorem pow_val_mul' (hζ : ζ ^ N = 1) (x y : ZMod N) :
    ζ ^ (x * y).val = (ζ ^ x.val) ^ y.val := by
  have h : x * y = ((x.val * y.val : ℕ) : ZMod N) := by push_cast; simp
  rw [h, pow_val_natCast' hζ, pow_mul]

theorem pow_val_neg' (hζ : ζ ^ N = 1) (x : ZMod N) :
    (ζ ^ (N - 1)) ^ x.val = ζ ^ (-x).val := by
  rw [← pow_mul, ← pow_val_natCast' hζ]
  congr 2
  rw [Nat.cast_mul, Nat.cast_sub (NeZero.one_le), ZMod.natCast_self, ZMod.natCast_zmod_val]
  ring

/-- Orthogonality from the principal property alone. -/
theorem sum_pow_val_principal (h : IsPrincipalRoot ζ N) (m : ZMod N) :
    ∑ j : ZMod N, ζ ^ (j * m).val = if m = 0 then (N : S) else 0 := by
  have hj : ∀ j : ZMod N, ζ ^ (j * m).val = ζ ^ (j.val * m.val) := by
    intro j
    rw [pow_val_mul' h.1, pow_mul]
  simp_rw [hj]
  rw [sum_range_pow_val (fun n => ζ ^ (n * m.val))]
  split_ifs with hm
  · subst hm
    simp
  · refine h.2 m.val ?_ (ZMod.val_lt m)
    exact Nat.pos_of_ne_zero (fun h0 => hm ((ZMod.val_eq_zero m).1 h0))

theorem dft_dft_principal (h : IsPrincipalRoot ζ N) (a : ZMod N → S) :
    dft ζ (dft ζ a) = fun k => (N : S) * a (-k) := by
  funext k
  simp only [dft, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hij : ∀ i j : ZMod N,
      ζ ^ (j * k).val * (ζ ^ (i * j).val * a i) = a i * ζ ^ (j * (i + k)).val := by
    intro i j
    rw [mul_add, pow_val_add' h.1, mul_comm i j]
    ring
  simp_rw [hij, ← Finset.mul_sum, sum_pow_val_principal h, add_eq_zero_iff_eq_neg, mul_ite,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

/-- Transforming with the inverse root undoes the transform up to the factor `N`. -/
theorem dft_inv_dft_principal (h : IsPrincipalRoot ζ N) (a : ZMod N → S) :
    dft (ζ ^ (N - 1)) (dft ζ a) = fun k => (N : S) * a k := by
  funext k
  simp only [dft, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hij : ∀ i j : ZMod N,
      (ζ ^ (N - 1)) ^ (j * k).val * (ζ ^ (i * j).val * a i) = a i * ζ ^ (j * (i - k)).val := by
    intro i j
    rw [pow_val_neg' h.1, ← mul_assoc, ← pow_val_add' h.1,
      show -(j * k) + i * j = j * (i - k) by ring]
    ring
  simp_rw [hij, ← Finset.mul_sum, sum_pow_val_principal h, sub_eq_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

end ZMod

/-! ### Vanishing sums from a half-period sign flip -/

theorem sum_pow_eq_zero_of_pow_half (ξ : S) (n : ℕ) (hξ : ξ ^ n = -1) :
    ∑ j ∈ Finset.range (2 * n), ξ ^ j = 0 := by
  rw [two_mul, Finset.sum_range_add]
  simp only [pow_add, hξ, neg_one_mul, Finset.sum_neg_distrib, add_neg_cancel]

theorem sum_pow_range_mul_eq_zero (ξ : S) (c n : ℕ) (h : ∑ j ∈ Finset.range n, ξ ^ j = 0) :
    ∑ j ∈ Finset.range (c * n), ξ ^ j = 0 := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih]
    simp only [pow_add, ← Finset.mul_sum, h, mul_zero, add_zero]

/-! ### The synthetic ring `ℂ[y]/(y^r + 1)` -/

/-- The coefficient ring `R = ℂ[y]/(y^r + 1)` of the paper's synthetic transforms. -/
abbrev SynthRing (r : ℕ) := AdjoinRoot ((Polynomial.X : Polynomial ℂ) ^ r + 1)

/-- The class of `y`. -/
noncomputable def synthY (r : ℕ) : SynthRing r := AdjoinRoot.root _

theorem synthY_pow_r (r : ℕ) : synthY r ^ r = -1 := by
  have h := AdjoinRoot.mk_self (f := (Polynomial.X : Polynomial ℂ) ^ r + 1)
  rw [← AdjoinRoot.aeval_eq] at h
  simp only [map_add, map_pow, Polynomial.aeval_X, map_one] at h
  exact eq_neg_of_add_eq_zero_left h

theorem synthY_pow_two_r (r : ℕ) : synthY r ^ (2 * r) = 1 := by
  rw [mul_comm, pow_mul, synthY_pow_r]
  norm_num

/-- `y^(2r/t)` is a principal `t`-th root of unity whenever `t ∣ 2r` are powers of two. -/
theorem synth_root_principal {r t e f : ℕ} (hr : r = 2 ^ e) (ht : t = 2 ^ f) (hf : f ≤ e + 1) :
    IsPrincipalRoot (synthY r ^ (2 * r / t)) t := by
  subst hr ht
  have h2r : 2 * 2 ^ e = 2 ^ (e + 1) := by rw [pow_succ, mul_comm]
  have hq : 2 * 2 ^ e / 2 ^ f = 2 ^ (e + 1 - f) := by
    rw [h2r, Nat.pow_div hf (by norm_num)]
  refine ⟨?_, fun m hm hmt => ?_⟩
  · rw [← pow_mul, hq, ← pow_add, show e + 1 - f + f = e + 1 by omega, ← h2r]
    exact synthY_pow_two_r _
  · obtain ⟨a, m', hm', rfl⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.pos_iff_ne_zero.1 hm)
    have haf : a < f := by
      have h1 : 2 ^ a ≤ 2 ^ a * m' := Nat.le_mul_of_pos_right _ hm'.pos
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt h1 hmt)
    -- rewrite the sum as powers of `ξ := y^(q m)`
    have hrw : ∀ j : ℕ, (synthY (2 ^ e) ^ (2 * 2 ^ e / 2 ^ f)) ^ (j * (2 ^ a * m'))
        = ((synthY (2 ^ e) ^ (2 * 2 ^ e / 2 ^ f)) ^ (2 ^ a * m')) ^ j := by
      intro j
      rw [mul_comm j, pow_mul]
    simp_rw [hrw]
    set ξ := (synthY (2 ^ e) ^ (2 * 2 ^ e / 2 ^ f)) ^ (2 ^ a * m') with hξ
    have hhalf : ξ ^ (2 ^ (f - a - 1)) = -1 := by
      rw [hξ, hq, ← pow_mul, ← pow_mul,
        show 2 ^ (e + 1 - f) * (2 ^ a * m' * 2 ^ (f - a - 1)) = 2 ^ e * m' by
          rw [show 2 ^ (e + 1 - f) * (2 ^ a * m' * 2 ^ (f - a - 1))
              = 2 ^ (e + 1 - f) * 2 ^ a * 2 ^ (f - a - 1) * m' by ring,
            ← pow_add, ← pow_add, show e + 1 - f + a + (f - a - 1) = e by omega],
        pow_mul, synthY_pow_r, hm'.neg_one_pow]
    have hsplit : 2 ^ f = 2 ^ a * (2 * 2 ^ (f - a - 1)) := by
      rw [← pow_succ', ← pow_add, show a + (f - a - 1 + 1) = f by omega]
    rw [hsplit]
    exact sum_pow_range_mul_eq_zero ξ _ _ (sum_pow_eq_zero_of_pow_half ξ _ hhalf)

/-- The radix-2 recursion computes the synthetic transform exactly. -/
theorem synth_fft_eq {e f : ℕ} (hf : f ≤ e + 1) (a : Fin (2 ^ f) → SynthRing (2 ^ e)) :
    fft f (synthY (2 ^ e) ^ (2 * 2 ^ e / 2 ^ f)) a
      = dftFin (synthY (2 ^ e) ^ (2 * 2 ^ e / 2 ^ f)) a :=
  fft_eq_dftFin f _ (synth_root_principal rfl rfl hf).1 a

/-- Synthetic transform inversion: `G_{ω⁻¹} (G_ω a) = t • a` in `ℂ[y]/(y^r+1)`. -/
theorem synth_dft_inv {e f : ℕ} (hf : f ≤ e + 1) (a : ZMod (2 ^ f) → SynthRing (2 ^ e)) :
    dft ((synthY (2 ^ e) ^ (2 * 2 ^ e / 2 ^ f)) ^ (2 ^ f - 1))
        (dft (synthY (2 ^ e) ^ (2 * 2 ^ e / 2 ^ f)) a)
      = fun k => ((2 ^ f : ℕ) : SynthRing (2 ^ e)) * a k :=
  dft_inv_dft_principal (synth_root_principal rfl rfl hf) a

end IntegerMultBounds.NLogN
