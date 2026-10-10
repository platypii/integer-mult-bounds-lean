import IntegerMultBounds.Spec.SignedRingProduct

/-! Sanity facts for the signed ring product's formats: the code `Γ` is
self-delimiting and the header reads back as `p, r, w`; component words have
width `w` and decode to the integer they encode; disk grid numerators fit the
width `w ≥ p + 2` and give coefficients of modulus at most one; a record has
`2 r w` bits. -/

namespace IntegerMultBounds.Spec.SignedRingProduct

open Machine NLogN

/-! ### `Γ` -/

theorem takeWhile_replicate_false (l : List Bool) : ∀ k : ℕ,
    (List.replicate k false ++ true :: l).takeWhile (· = false) = List.replicate k false
  | 0 => by simp
  | k + 1 => by
    rw [List.replicate_succ, List.cons_append, List.takeWhile_cons_of_pos (by simp),
      takeWhile_replicate_false l k]

theorem msbBits_size {v : ℕ} (hv : 1 ≤ v) :
    msbBits (Nat.size v) v = true :: msbBits (Nat.size v - 1) v := by
  have hpos := Nat.size_pos.mpr hv
  have hlo : 2 ^ (Nat.size v - 1) ≤ v := Nat.lt_size.mp (by omega)
  have hhi : v < 2 ^ Nat.size v := Nat.lt_size_self v
  have e : Nat.size v = Nat.size v - 1 + 1 := by omega
  have hd : v / 2 ^ (Nat.size v - 1) = 1 := by
    apply Nat.div_eq_of_lt_le (by simpa using hlo)
    rw [show (1 + 1) * 2 ^ (Nat.size v - 1) = 2 ^ (Nat.size v - 1 + 1) by rw [pow_succ]; ring, ← e]
    exact hhi
  conv_lhs => rw [e]
  rw [msbBits, hd]
  rfl

theorem gammaRead_gamma {v : ℕ} (hv : 1 ≤ v) (rest : List Bool) :
    gammaRead (gamma v ++ rest) = some (v, rest) := by
  have hpos := Nat.size_pos.mpr hv
  have hm := msbBits_size hv
  set k := Nat.size v - 1 with hk
  have hn : Nat.size v = k + 1 := by omega
  have hg : gamma v ++ rest = List.replicate k false ++ true :: (msbBits k v ++ rest) := by
    rw [gamma, hm, ← hk]; simp
  have ht : (gamma v ++ rest).takeWhile (· = false) = List.replicate k false := by
    rw [hg]; exact takeWhile_replicate_false _ k
  have hdrop : (gamma v ++ rest).drop k = msbBits (Nat.size v) v ++ rest := by
    rw [hg, hm]; simp
  unfold gammaRead
  simp only [ht, List.length_replicate, hdrop, List.length_append, length_msbBits]
  rw [if_neg (by omega), ← hn, List.take_left' (length_msbBits _ _), List.drop_left' (length_msbBits _ _),
    binaryValue_msbBits, Nat.mod_eq_of_lt (Nat.lt_size_self v)]

theorem header_read (p r w : ℕ) (hp : 1 ≤ p) (hr : 1 ≤ r) (hw : 1 ≤ w) :
    ((gammaRead (header p r w)).bind fun x => ((gammaRead x.2).bind fun y =>
      (gammaRead y.2).map fun z => (x.1, y.1, z.1))) = some (p, r, w) := by
  have h3 := gammaRead_gamma hw []
  rw [List.append_nil] at h3
  rw [header, List.append_assoc, gammaRead_gamma hp]
  simp [gammaRead_gamma hr, h3]

/-! ### Component words -/

@[simp] theorem length_compWord (w : ℕ) (z : ℤ) : (compWord w z).length = w := by simp [compWord]

theorem compValue_compWord {w : ℕ} {z : ℤ} (hw : 1 ≤ w) (h1 : -2 ^ (w - 1) ≤ z) (h2 : z < 2 ^ (w - 1)) :
    compValue (compWord w z) = z := by
  obtain ⟨m, rfl⟩ : ∃ m, w = m + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2
  have hP : (2 : ℤ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have hpos : (0 : ℤ) < 2 ^ m := by positivity
  set N := (z % 2 ^ (m + 1)).toNat with hN
  have hz0 : 0 ≤ z % 2 ^ (m + 1) := Int.emod_nonneg _ (by positivity)
  have hNc : (N : ℤ) = z % 2 ^ (m + 1) := Int.toNat_of_nonneg hz0
  have hNlt : N < 2 ^ (m + 1) := by
    have h := Int.emod_lt_of_pos z (show (0 : ℤ) < 2 ^ (m + 1) by positivity)
    rw [← hNc] at h
    exact_mod_cast h
  unfold compValue compWord
  rw [← hN, binaryValue_msbBits, Nat.mod_eq_of_lt hNlt, length_msbBits, msbBits]
  simp only [List.headD_cons]
  by_cases hz : 0 ≤ z
  · have e : z % 2 ^ (m + 1) = z := Int.emod_eq_of_lt hz (by rw [hP]; omega)
    have hNz : (N : ℤ) = z := by rw [hNc, e]
    have hd : N / 2 ^ m = 0 := Nat.div_eq_of_lt (by zify; rw [hNz]; exact h2)
    rw [hd]; simp [hNz]
  · have e : z % 2 ^ (m + 1) = z + 2 ^ (m + 1) := by
      rw [← Int.add_mul_emod_self_left z (2 ^ (m + 1)) 1, mul_one, Int.emod_eq_of_lt (by rw [hP]; omega)
        (by rw [hP]; omega)]
    have hNz : (N : ℤ) = z + 2 ^ (m + 1) := by rw [hNc, e]
    have hd : N / 2 ^ m = 1 := by
      apply Nat.div_eq_of_lt_le (by zify; rw [hNz]; rw [hP]; omega)
      rw [show (1 + 1) * 2 ^ m = 2 ^ (m + 1) by rw [pow_succ]; ring]; exact hNlt
    rw [hd]; simp [hNz]

/-! ### Disk grid numerators -/

theorem DiskGrid.abs_le {r p : ℕ} {re im : Fin r → ℤ} (h : DiskGrid p re im) (j : Fin r) :
    |re j| ≤ 2 ^ p ∧ |im j| ≤ 2 ^ p := by
  have hj := h j
  have e : (2 : ℤ) ^ (2 * p) = (2 ^ p) ^ 2 := by rw [pow_mul']
  rw [e] at hj
  have hp : (0 : ℤ) ≤ 2 ^ p := by positivity
  constructor
  · exact _root_.abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (im j)]) hp)
  · exact _root_.abs_le.mpr (abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg (re j)]) hp)

theorem DiskGrid.fits {r p w : ℕ} {re im : Fin r → ℤ} (h : DiskGrid p re im) (hw : p + 2 ≤ w) (j : Fin r) :
    compValue (compWord w (re j)) = re j ∧ compValue (compWord w (im j)) = im j := by
  obtain ⟨h1, h2⟩ := h.abs_le j
  have hlt : (2 : ℤ) ^ p < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  rw [_root_.abs_le] at h1 h2
  exact ⟨compValue_compWord (by omega) (by linarith) (by linarith),
    compValue_compWord (by omega) (by linarith) (by linarith)⟩

theorem DiskGrid.norm_le {r p : ℕ} {re im : Fin r → ℤ} (h : DiskGrid p re im) (j : Fin r) :
    ‖gridPoly p re im j‖ ≤ 1 := by
  have hj : ((re j : ℝ)) ^ 2 + (im j : ℝ) ^ 2 ≤ (2 ^ p) ^ 2 := by
    have := h j
    have e : (2 : ℤ) ^ (2 * p) = (2 ^ p) ^ 2 := by rw [pow_mul']
    rw [e] at this
    exact_mod_cast this
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  rw [Complex.norm_def, Real.sqrt_le_one, Complex.normSq_apply]
  simp only [gridPoly]
  rw [div_mul_div_comm, div_mul_div_comm, ← add_div, div_le_one (by positivity)]
  nlinarith

/-! ### Records -/

theorem length_record {r : ℕ} (w : ℕ) (re im : Fin r → ℤ) : (record w re im).length = 2 * r * w := by
  simp [record, List.length_flatMap, List.map_const']
  ring

end IntegerMultBounds.Spec.SignedRingProduct
