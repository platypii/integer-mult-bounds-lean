import IntegerMultBounds.NLogN.SynthEmbed

/-! The `d`-dimensional synthetic transform of Harvey and van der Hoeven,
Sections 2.4 and 3.1, in coefficient form over `R = ℂ[y]/(y^r + 1)`: the
`R`-valued analogue of `dftD`. Arrays are indexed by `(i : Fin d) → Fin (N i)`
with every `N i ∣ 2r`, and the transform multiplies by the product of the
shifts `y^((2r/N i) j_i k_i)`. Proved: the splitting of the first coordinate
into a one-dimensional synthetic transform of lower-dimensional transforms,
the convolution theorem (the transform of `synthConvG` is `∏ N i` times the
pointwise negacyclic product), orthogonality and inversion when every `N i`
is a power of two, and the sup-norm contraction of both transforms. Fixed
point errors are not treated here. -/

namespace IntegerMultBounds.NLogN

section MultiD

variable {r : ℕ} [NeZero r] {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

/-- The exponent of the shift attached to the index pair `(j, k)`. -/
def synthExp (r : ℕ) (N : Fin d → ℕ) (j k : (i : Fin d) → Fin (N i)) : ℕ :=
  ∑ i, (2 * r / N i) * (j i).val * (k i).val

/-- The `d`-dimensional synthetic transform, normalised by `1/∏ N i`. -/
noncomputable def synthDFTD (r : ℕ) (N : Fin d → ℕ)
    (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
  fun j => (1 / ((∏ i, N i : ℕ) : ℂ)) • ∑ k, shiftNegZ (synthExp r N j k) (u k)

omit [NeZero r] [∀ i, NeZero (N i)] in
theorem synthExp_comm (j k : (i : Fin d) → Fin (N i)) :
    synthExp r N j k = synthExp r N k j := by
  unfold synthExp
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Shifts depend on the exponent only modulo `2r`. -/
theorem shiftNegZ_congr_mod {e₁ e₂ : ℕ} (h : e₁ % (2 * r) = e₂ % (2 * r)) (a : Fin r → ℂ) :
    shiftNegZ e₁ a = shiftNegZ e₂ a := by
  rw [shiftNegZ_mod e₁, shiftNegZ_mod e₂, h]

omit [NeZero r] [∀ i, NeZero (N i)] in
/-- Reducing one coordinate modulo `N i` changes the exponent by a multiple of `2r`. -/
theorem coord_exp_mod (hN : ∀ i, N i ∣ 2 * r) (i : Fin d) (j a : ℕ) :
    (2 * r / N i) * j * a % (2 * r) = (2 * r / N i) * j * (a % N i) % (2 * r) := by
  have hct : 2 * r / N i * N i = 2 * r := Nat.div_mul_cancel (hN i)
  conv_lhs => rw [← Nat.mod_add_div a (N i)]
  have h : 2 * r / N i * j * (a % N i + N i * (a / N i))
      = 2 * r / N i * j * (a % N i) + (2 * r / N i * N i) * (j * (a / N i)) := by ring
  rw [h, hct, Nat.add_mul_mod_self_left]

omit [NeZero r] [∀ i, NeZero (N i)] in
/-- The exponent at a sum of indices agrees modulo `2r` with the sum of exponents. -/
theorem synthExp_add_mod (hN : ∀ i, N i ∣ 2 * r) (j i m : (l : Fin d) → Fin (N l)) :
    synthExp r N j (i + m) % (2 * r) = (synthExp r N j i + synthExp r N j m) % (2 * r) := by
  unfold synthExp
  rw [← Finset.sum_add_distrib, Finset.sum_nat_mod, Finset.sum_nat_mod (f := fun l =>
    2 * r / N l * (j l).val * (i l).val + 2 * r / N l * (j l).val * (m l).val)]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.add_apply, Fin.val_add, ← mul_add]
  exact (coord_exp_mod hN l _ _).symm

/-- The convolution theorem: the transform of a convolution is `∏ N i` times the
pointwise negacyclic product of the transforms. -/
theorem synthDFTD_conv (hN : ∀ i, N i ∣ 2 * r)
    (u v : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) :
    synthDFTD r N (synthConvG u v)
      = fun j => ((∏ i, N i : ℕ) : ℂ) • negacyclicMul (synthDFTD r N u j) (synthDFTD r N v j) := by
  funext j
  have hT : ((∏ i, N i : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (N i)
  have key : ∑ k, shiftNegZ (synthExp r N j k) (synthConvG u v k)
      = ∑ i, ∑ m, negacyclicMul (shiftNegZ (synthExp r N j i) (u i))
          (shiftNegZ (synthExp r N j m) (v m)) := by
    simp only [synthConvG, shiftNegZ_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Fintype.sum_equiv (Equiv.addLeft i)
      (fun m => shiftNegZ (synthExp r N j (i + m)) (negacyclicMul (u i) (v (i + m - i))))
      (fun k => shiftNegZ (synthExp r N j k) (negacyclicMul (u i) (v (k - i))))
      (fun m => rfl)]
    apply Finset.sum_congr rfl
    intro m _
    rw [add_sub_cancel_left, shiftNegZ_congr_mod (synthExp_add_mod hN j i m), Nat.add_comm,
      ← shiftNegZ_add,
      shiftNegZ_negacyclicMul, negacyclicMul_comm, shiftNegZ_negacyclicMul, negacyclicMul_comm]
  simp only [synthDFTD]
  rw [key, negacyclicMul_smul_left, negacyclicMul_smul_right, smul_smul, smul_smul,
    negacyclicMul_sum_left]
  simp only [negacyclicMul_sum_right]
  congr 1
  field_simp

/-- Splitting the first coordinate: a `(d+1)`-dimensional synthetic transform is a
one-dimensional synthetic transform along the first axis of the `d`-dimensional
transforms of the slices. -/
theorem synthDFTD_succ {N : Fin (d + 1) → ℕ} [∀ i, NeZero (N i)]
    (u : ((i : Fin (d + 1)) → Fin (N i)) → (Fin r → ℂ)) :
    synthDFTD r N u = fun j => synthDFT r (N 0)
      (fun j₀ => synthDFTD r (fun i => N i.succ) (fun k' => u (Fin.cons j₀ k')) (Fin.tail j))
      (j 0) := by
  funext j
  simp only [synthDFTD, synthDFT, shiftNegZ_sum, shiftNegZ_smul, Finset.smul_sum, smul_smul]
  rw [← Equiv.sum_comp (Fin.consEquiv fun i => Fin (N i)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j₀ _ => Finset.sum_congr rfl fun j' _ => ?_
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.tail, synthExp, Fin.sum_univ_succ]
  rw [shiftNegZ_add]
  congr 1
  push_cast
  ring

end MultiD

section Inversion

variable {r : ℕ} [NeZero r] {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

omit [NeZero r] in
theorem synthExp_zero_left (k : (i : Fin d) → Fin (N i)) : synthExp r N 0 k = 0 := by
  simp [synthExp]

/-- Orthogonality: for nonzero `m` the shifts `y^(exp m k)` sum to zero over `k`. -/
theorem sum_shiftNegZ_prod_eq_zero (hN : ∀ i, N i ∣ 2 * r) (hpow : ∀ i, ∃ f, N i = 2 ^ f)
    (m : (i : Fin d) → Fin (N i)) (hm : m ≠ 0) (a : Fin r → ℂ) :
    ∑ k, shiftNegZ (synthExp r N m k) a = 0 := by
  induction d with
  | zero => exact absurd (Subsingleton.elim m 0) hm
  | succ d ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv fun i => Fin (N i)), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    have hsplit : ∀ (k₀ : Fin (N 0)) (k' : (i : Fin d) → Fin (N i.succ)),
        synthExp r N m (Fin.cons k₀ k')
          = (2 * r / N 0) * (m 0).val * k₀.val
            + synthExp r (fun i => N i.succ) (Fin.tail m) k' := by
      intro k₀ k'
      simp only [synthExp, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
    simp only [hsplit, ← shiftNegZ_add]
    by_cases h0 : m 0 = 0
    · -- the tail of `m` is nonzero; use the induction hypothesis on the inner sum
      have htail : Fin.tail m ≠ 0 := by
        intro ht
        apply hm
        funext i
        induction i using Fin.cases with
        | zero => exact h0
        | succ i => exact congrFun ht i
      refine Finset.sum_eq_zero fun k₀ _ => ?_
      rw [← shiftNegZ_sum, ih (fun i => hN i.succ) (fun i => hpow i.succ) (Fin.tail m) htail,
        ← shiftZCLM_apply, map_zero]
    · -- the head of `m` is nonzero; the outer sum vanishes by one-dimensional orthogonality
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k' _ => ?_
      obtain ⟨f, hf⟩ := hpow 0
      have hpos : 0 < (m 0).val := Nat.pos_of_ne_zero (fun h => h0 (Fin.ext h))
      have := sum_shiftNegZ_eq_zero (hN 0) hf hpos (m 0).isLt
        (shiftNegZ (synthExp r (fun i => N i.succ) (Fin.tail m) k') a)
      exact this

/-- The inverse `d`-dimensional transform, at the inverse roots. -/
noncomputable def synthDFTDInv (r : ℕ) (N : Fin d → ℕ)
    (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ) :=
  fun j => (1 / ((∏ i, N i : ℕ) : ℂ)) • ∑ k, shiftNegZ (synthExp r N (-j) k) (u k)

omit [NeZero r] in
theorem synthExp_neg_add_mod (hN : ∀ i, N i ∣ 2 * r) (j i : (l : Fin d) → Fin (N l))
    (k : (l : Fin d) → Fin (N l)) :
    (synthExp r N (-j) k + synthExp r N i k) % (2 * r) = synthExp r N (i - j) k % (2 * r) := by
  rw [synthExp_comm (-j), synthExp_comm i, synthExp_comm (i - j), sub_eq_add_neg, add_comm i,
    synthExp_add_mod hN]

/-- Inversion: `F_inv (F u) = u / ∏ N i` when every length is a power of two. -/
theorem synthDFTDInv_synthDFTD (hN : ∀ i, N i ∣ 2 * r) (hpow : ∀ i, ∃ f, N i = 2 ^ f)
    (u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)) :
    synthDFTDInv r N (synthDFTD r N u) = fun j => (1 / ((∏ i, N i : ℕ) : ℂ)) • u j := by
  funext j
  have hT : ((∏ i, N i : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (N i)
  simp only [synthDFTDInv, synthDFTD, shiftNegZ_sum, shiftNegZ_smul, Finset.smul_sum, smul_smul,
    shiftNegZ_add]
  rw [Finset.sum_comm]
  have hterm : ∀ i, ∑ k, (1 / ((∏ l, N l : ℕ) : ℂ) * (1 / ((∏ l, N l : ℕ) : ℂ))) •
      shiftNegZ (synthExp r N (-j) k + synthExp r N k i) (u i)
      = if i = j then (1 / ((∏ l, N l : ℕ) : ℂ)) • u j else 0 := by
    intro i
    have hexp : ∀ k, shiftNegZ (synthExp r N (-j) k + synthExp r N k i) (u i)
        = shiftNegZ (synthExp r N (i - j) k) (u i) := by
      intro k
      rw [synthExp_comm k i]
      exact shiftNegZ_congr_mod (synthExp_neg_add_mod hN j i k) _
    simp only [hexp]
    by_cases hij : i = j
    · subst hij
      simp only [sub_self, synthExp_zero_left, shiftNegZ_zero, Finset.sum_const,
        Finset.card_univ, Fintype.card_pi, Fintype.card_fin, ← smul_assoc, nsmul_eq_mul,
        ↓reduceIte]
      congr 1
      push_cast
      field_simp
    · rw [ite_eq_right hij, ← Finset.smul_sum, sum_shiftNegZ_prod_eq_zero hN hpow (i - j)
        (sub_ne_zero.mpr hij), smul_zero]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Inversion

section Norms

variable {r : ℕ} [NeZero r] {d : ℕ} {N : Fin d → ℕ} [∀ i, NeZero (N i)]

theorem norm_sum_shift_le {A : ℝ} (e : ((i : Fin d) → Fin (N i)) → ℕ)
    {u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)} (hA : ∀ j, ‖u j‖ ≤ A) :
    ‖(1 / ((∏ i, N i : ℕ) : ℂ)) • ∑ k, shiftNegZ (e k) (u k)‖ ≤ A := by
  have hT : (0 : ℝ) < (∏ i, N i : ℕ) := by
    exact_mod_cast Finset.prod_pos fun i _ => NeZero.pos (N i)
  rw [norm_smul, norm_div, norm_one, Complex.norm_natCast]
  calc 1 / ((∏ i, N i : ℕ) : ℝ) * ‖∑ k, shiftNegZ (e k) (u k)‖
      ≤ 1 / ((∏ i, N i : ℕ) : ℝ) * ∑ k : (i : Fin d) → Fin (N i), A := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        exact (norm_shiftNegZ_le _ _).trans (hA k)
    _ = A := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_pi, nsmul_eq_mul]
        simp only [Fintype.card_fin]
        field_simp

/-- The `d`-dimensional synthetic transform is a contraction in the sup norm. -/
theorem norm_synthDFTD_le {A : ℝ} {u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)}
    (hA : ∀ j, ‖u j‖ ≤ A) (j : (i : Fin d) → Fin (N i)) : ‖synthDFTD r N u j‖ ≤ A :=
  norm_sum_shift_le _ hA

theorem norm_synthDFTDInv_le {A : ℝ} {u : ((i : Fin d) → Fin (N i)) → (Fin r → ℂ)}
    (hA : ∀ j, ‖u j‖ ≤ A) (j : (i : Fin d) → Fin (N i)) : ‖synthDFTDInv r N u j‖ ≤ A :=
  norm_sum_shift_le _ hA

end Norms

end IntegerMultBounds.NLogN
