module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# Port isometries of the compressed nine-stage geometry

Upstream's compressed geometry (`nine/geometry.py`) gives each port `t` its line `q` (an E8 root of
norm `4` under the dot product, norm `2` under the form `⟨x, y⟩/2`) and an orthonormal basis `A` of
the orthogonal space of `q`, the last seven columns of a Weyl element mapping line zero to `q`.
* `PortCertificate` stores `q` and `2A`, both integral; `Checked` is the integer form of
  `qᵀq = 4`, `AᵀA = 1`, `AAᵀ + qqᵀ/4 = 1` and `qᵀA = 0`.
* `lineProj = qqᵀ/4` is the orthogonal projector onto the line, `1 - lineProj` the one onto its
  orthogonal space.
* `rho = [[P, A], [Aᵀ, 0]]` is upstream's stage map on the eight local and seven exterior axes.
  `rho_transpose` and `rho_mul_self` show it is a symmetric involution, hence an isometry.
  `rho_conj_line`, `rho_conj_one`, `rho_conj_zero` and `rho_conj_complement` are upstream's four
  conjugation identities: `ρ (U ⊕ 1) ρ` for `U = P, 1, 0, 1 - P`.
* `exchange U = [[1 - U, U], [U, 1 - U]]` is the bit address operator `D_U`, which exchanges the
  `U`-components of the two address halves. `exchange_one_mul` is upstream's `D_1 D_P = D_(1-P)`,
  and `exchange_mul_self` its `D_P² = 1`. Exchanges compose additively when `UV = 0`
  (`exchange_mul_of_orthogonal`), a nested frame change is the exchange on the projector
  difference (`exchange_change`), and an invertible coordinate change conjugates `D_U` to the
  exchange on the conjugated projector (`exchange_conj`).
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

open Matrix

/-- A port's line `q` and twice its complement columns. -/
structure PortCertificate where
  line : Fin 8 → ℤ
  twiceComplement : Fin 8 → Fin 7 → ℤ

instance : Inhabited PortCertificate := ⟨⟨0, 0⟩⟩

namespace PortCertificate

/-- The integer orthonormality equations of the line and the complement columns. -/
def Checked (c : PortCertificate) : Prop :=
  ∑ i, c.line i * c.line i = 4 ∧
  (∀ k l, ∑ i, c.twiceComplement i k * c.twiceComplement i l = if k = l then 4 else 0) ∧
  (∀ i j, ∑ k, c.twiceComplement i k * c.twiceComplement j k + c.line i * c.line j =
    if i = j then 4 else 0) ∧
  ∀ k, ∑ i, c.line i * c.twiceComplement i k = 0

instance (c : PortCertificate) : Decidable c.Checked := inferInstanceAs
  (Decidable (∑ i, c.line i * c.line i = 4 ∧
    (∀ k l, ∑ i, c.twiceComplement i k * c.twiceComplement i l = if k = l then 4 else 0) ∧
    (∀ i j, ∑ k, c.twiceComplement i k * c.twiceComplement j k + c.line i * c.line j =
      if i = j then 4 else 0) ∧
    ∀ k, ∑ i, c.line i * c.twiceComplement i k = 0))

/-- The orthogonal projector `qqᵀ/4` onto the port's line. -/
def lineProj (c : PortCertificate) : Matrix (Fin 8) (Fin 8) ℚ :=
  of fun i j => (c.line i : ℚ) * c.line j / 4

/-- The complement columns `A`. -/
def complement (c : PortCertificate) : Matrix (Fin 8) (Fin 7) ℚ :=
  of fun i k => (c.twiceComplement i k : ℚ) / 2

/-- The stage map `ρ = [[P, A], [Aᵀ, 0]]` on the local and exterior axes. -/
def rho (c : PortCertificate) : Matrix (Fin 8 ⊕ Fin 7) (Fin 8 ⊕ Fin 7) ℚ :=
  fromBlocks c.lineProj c.complement c.complementᵀ 0

variable {c : PortCertificate}

/-- Project onto the certified port line along the coordinate hyperplane at its first pivot.
The two absorption identities identify the image with the original port projector's image. -/
theorem exists_triangular_lineProj (h : c.Checked) :
    ∃ (p : Fin 8) (U : Matrix (Fin 8) (Fin 8) ℚ), U.IsLowerTriangular ∧
      U * c.lineProj = c.lineProj ∧ c.lineProj * U = U ∧ U * U = U ∧
      ∀ i, U i i = if i = p then 1 else 0 := by
  let support := Finset.univ.filter fun i => c.line i ≠ 0
  have nonempty : support.Nonempty := by
    by_contra hn
    have zero (i) : c.line i = 0 := by
      by_contra hi
      exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simpa [zero] using h.1
  let p := support.min' nonempty
  have hp : c.line p ≠ 0 := (Finset.mem_filter.mp (support.min'_mem nonempty)).2
  have hpq : (c.line p : ℚ) ≠ 0 := by exact_mod_cast hp
  let U : Matrix (Fin 8) (Fin 8) ℚ := of fun i j => if j = p then c.line i / (c.line p : ℚ) else 0
  have project (M : Matrix (Fin 8) (Fin 8) ℚ) (i j) :
      (U * M) i j = (c.line i / (c.line p : ℚ)) * M p j := by
    simp [mul_apply, U, ite_mul]
  refine ⟨p, U, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    change i < j at hij
    by_cases hj : j = p
    · subst j
      have hi : c.line i = 0 := by
        by_contra nz
        exact hij.not_ge (support.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, nz⟩))
      simp [U, hi]
    · simp [U, hj]
  · ext i j
    rw [project]
    simp only [lineProj, of_apply]
    field_simp
  · ext i j
    by_cases hj : j = p
    · subst j
      have norm := congrArg (Int.cast : ℤ → ℚ) h.1
      push_cast at norm
      simp only [mul_apply, lineProj, U, of_apply, ite_true, eq_self]
      calc ∑ k, (c.line i : ℚ) * c.line k / 4 * (c.line k / c.line p) =
          (c.line i / (4 * (c.line p : ℚ))) * ∑ k, (c.line k : ℚ) * c.line k := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun _ _ => by ring
        _ = _ := by rw [norm]; ring
    · simp [mul_apply, U, hj]
  · ext i j
    rw [project]
    by_cases hj : j = p <;> simp [U, hj, hpq]
  · intro i
    by_cases hi : i = p <;> simp [U, hi, hpq]

/-- Preserving the target hyperplane as well as the source line forces the original
projector. A port with two nonzero coordinates therefore has no triangular replacement
that preserves both images via complementary frames. -/
theorem incompatible_port_frames {i j : Fin 8} (hij : i < j)
    (hi : c.line i ≠ 0) (hj : c.line j ≠ 0) (U : Matrix (Fin 8) (Fin 8) ℚ)
    (lower : U.IsLowerTriangular) (source : U * c.lineProj = c.lineProj) :
    (1 - U) * (1 - c.lineProj) ≠ 1 - c.lineProj := by
  intro target
  rw [mul_sub, mul_one, sub_mul, one_mul, source, sub_self, sub_zero] at target
  have eq : U = c.lineProj := sub_right_inj.mp target
  have zero := lower (i := i) (j := j) hij
  rw [eq] at zero
  have nz : (c.line i : ℚ) * c.line j / 4 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero (by exact_mod_cast hi) (by exact_mod_cast hj)) (by norm_num)
  exact nz zero

theorem lineProj_transpose : c.lineProjᵀ = c.lineProj := by
  ext i j
  simp only [transpose_apply, lineProj, of_apply]
  ring

theorem lineProj_mul_self (h : c.Checked) : c.lineProj * c.lineProj = c.lineProj := by
  ext i j
  have hn := congrArg (Int.cast : ℤ → ℚ) h.1
  push_cast at hn
  simp only [mul_apply, lineProj, of_apply]
  calc ∑ k, (c.line i : ℚ) * c.line k / 4 * ((c.line k : ℚ) * c.line j / 4)
      = (c.line i : ℚ) * c.line j / 16 * ∑ k, (c.line k : ℚ) * c.line k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = (c.line i : ℚ) * c.line j / 4 := by rw [hn]; ring

theorem complement_orthonormal (h : c.Checked) : c.complementᵀ * c.complement = 1 := by
  ext k l
  have hkl := congrArg (Int.cast : ℤ → ℚ) (h.2.1 k l)
  push_cast at hkl
  simp only [mul_apply, transpose_apply, complement, of_apply, one_apply]
  calc ∑ i, (c.twiceComplement i k : ℚ) / 2 * ((c.twiceComplement i l : ℚ) / 2)
      = 1 / 4 * ∑ i, (c.twiceComplement i k : ℚ) * c.twiceComplement i l := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = if k = l then 1 else 0 := by rw [hkl]; split_ifs <;> norm_num

theorem complement_mul_transpose (h : c.Checked) :
    c.complement * c.complementᵀ = 1 - c.lineProj := by
  ext i j
  have hij := congrArg (Int.cast : ℤ → ℚ) (h.2.2.1 i j)
  push_cast at hij
  simp only [mul_apply, transpose_apply, complement, of_apply, Matrix.sub_apply, one_apply, lineProj]
  have hs : ∑ k, (c.twiceComplement i k : ℚ) / 2 * ((c.twiceComplement j k : ℚ) / 2) =
      1 / 4 * ∑ k, (c.twiceComplement i k : ℚ) * c.twiceComplement j k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hs, eq_sub_of_add_eq hij]
  split_ifs <;> ring

theorem lineProj_mul_complement (h : c.Checked) : c.lineProj * c.complement = 0 := by
  ext i k
  have hk := congrArg (Int.cast : ℤ → ℚ) (h.2.2.2 k)
  push_cast at hk
  simp only [mul_apply, lineProj, complement, of_apply, Matrix.zero_apply]
  calc ∑ j, (c.line i : ℚ) * c.line j / 4 * ((c.twiceComplement j k : ℚ) / 2)
      = (c.line i : ℚ) / 8 * ∑ j, (c.line j : ℚ) * c.twiceComplement j k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by rw [hk, mul_zero]

theorem transpose_complement_mul_lineProj (h : c.Checked) : c.complementᵀ * c.lineProj = 0 := by
  have ht := congrArg transpose (lineProj_mul_complement h)
  rwa [transpose_mul, lineProj_transpose, transpose_zero] at ht

theorem lineProj_mul_orth (h : c.Checked) : c.lineProj * (1 - c.lineProj) = 0 := by
  rw [mul_sub, mul_one, lineProj_mul_self h, sub_self]

theorem orth_mul_lineProj (h : c.Checked) : (1 - c.lineProj) * c.lineProj = 0 := by
  rw [sub_mul, one_mul, lineProj_mul_self h, sub_self]

theorem orth_mul_self (h : c.Checked) : (1 - c.lineProj) * (1 - c.lineProj) = 1 - c.lineProj := by
  rw [sub_mul, one_mul, lineProj_mul_orth h, sub_zero]

theorem rho_transpose : c.rhoᵀ = c.rho := by
  rw [rho, fromBlocks_transpose, transpose_transpose, transpose_zero, lineProj_transpose]

theorem rho_mul_self (h : c.Checked) : c.rho * c.rho = 1 := by
  rw [rho, fromBlocks_multiply, lineProj_mul_self h, complement_mul_transpose h,
    lineProj_mul_complement h, transpose_complement_mul_lineProj h, complement_orthonormal h]
  simp [← fromBlocks_one]

/-- `ρ (U ⊕ 1) ρ`, for any local frame `U`. -/
theorem rho_conj (h : c.Checked) (U : Matrix (Fin 8) (Fin 8) ℚ) :
    c.rho * fromBlocks U 0 0 1 * c.rho =
      fromBlocks (c.lineProj * U * c.lineProj + (1 - c.lineProj)) (c.lineProj * U * c.complement)
        (c.complementᵀ * U * c.lineProj) (c.complementᵀ * U * c.complement) := by
  simp only [rho, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    add_zero, zero_add, complement_mul_transpose h]

theorem rho_conj_line (h : c.Checked) :
    c.rho * fromBlocks c.lineProj 0 0 1 * c.rho = fromBlocks 1 0 0 0 := by
  rw [rho_conj h]
  simp [lineProj_mul_self h, lineProj_mul_complement h, transpose_complement_mul_lineProj h]

theorem rho_conj_one (h : c.Checked) : c.rho * fromBlocks 1 0 0 1 * c.rho = 1 := by
  rw [fromBlocks_one, Matrix.mul_one, rho_mul_self h]

theorem rho_conj_zero (h : c.Checked) :
    c.rho * fromBlocks 0 0 0 1 * c.rho = fromBlocks (1 - c.lineProj) 0 0 0 := by
  rw [rho_conj h]
  simp

theorem rho_conj_complement (h : c.Checked) :
    c.rho * fromBlocks (1 - c.lineProj) 0 0 1 * c.rho = fromBlocks (1 - c.lineProj) 0 0 1 := by
  rw [rho_conj h]
  simp [Matrix.mul_sub, lineProj_mul_self h, transpose_complement_mul_lineProj h,
    complement_orthonormal h]

/-- Adapt the complement columns to an oblique projector onto the certified line.
The resulting stage route is an involution and sends the line plus exterior frame
to the full local frame. -/
theorem oblique_line_route (h : c.Checked) (U : Matrix (Fin 8) (Fin 8) ℚ)
    (up : U * c.lineProj = c.lineProj) (pu : c.lineProj * U = U) :
    let B := (1 - U) * c.complement
    let R := fromBlocks U B c.complementᵀ 0
    R * R = 1 ∧ R * fromBlocks U 0 0 1 * R = fromBlocks 1 0 0 0 ∧
      R * fromBlocks 0 0 0 1 * R = fromBlocks (1 - U) 0 0 0 ∧
      R * fromBlocks (1 - U) 0 0 1 * R = fromBlocks (1 - U) 0 0 1 := by
  intro B R
  have idem : U * U = U := by
    calc U * U = U * (c.lineProj * U) := by rw [pu]
      _ = U := by rw [← Matrix.mul_assoc, up, pu]
  have annihilate : c.complementᵀ * U = 0 := by
    calc _ = c.complementᵀ * (c.lineProj * U) := by rw [pu]
         _ = 0 := by rw [← Matrix.mul_assoc, transpose_complement_mul_lineProj h, Matrix.zero_mul]
  have ub : U * B = 0 := by
    dsimp [B]
    rw [← Matrix.mul_assoc, mul_sub, mul_one, idem, sub_self, Matrix.zero_mul]
  have leftInv : c.complementᵀ * B = 1 := by
    dsimp [B]
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, annihilate, sub_zero, complement_orthonormal h]
  have rightInv : B * c.complementᵀ = 1 - U := by
    dsimp [B]
    rw [Matrix.mul_assoc, complement_mul_transpose h, mul_sub, mul_one, sub_mul, one_mul,
      up, sub_self, sub_zero]
  simp [R, fromBlocks_multiply, Matrix.mul_sub, idem, ub, annihilate, leftInv, rightInv,
    ← fromBlocks_one]

end PortCertificate

/-! ### The bit address operators -/

section Exchange

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bit address operator `D_U` on the two address halves. -/
def exchange (U : Matrix ι ι ℚ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ := fromBlocks (1 - U) U U (1 - U)

omit [Fintype ι] in
theorem exchange_zero : exchange (0 : Matrix ι ι ℚ) = 1 := by
  simp [exchange, fromBlocks_one]

/-- `D_1 D_U = D_(1-U)`. -/
theorem exchange_one_mul (U : Matrix ι ι ℚ) : exchange 1 * exchange U = exchange (1 - U) := by
  simp [exchange, fromBlocks_multiply]

/-- Exchanges compose additively when `U * V = 0`. -/
theorem exchange_mul_of_orthogonal {U V : Matrix ι ι ℚ} (hUV : U * V = 0) :
    exchange U * exchange V = exchange (U + V) := by
  simp only [exchange, fromBlocks_multiply, sub_mul, mul_sub, one_mul, mul_one, hUV]
  rw [fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> abel

theorem exchange_mul_self {U : Matrix ι ι ℚ} (hU : U * U = U) : exchange U * exchange U = 1 := by
  simp only [exchange, fromBlocks_multiply, sub_mul, mul_sub, one_mul, mul_one, hU]
  rw [← fromBlocks_one]
  congr 1 <;> abel

/-- A nested frame change `U ≤ V` is the exchange on the projector difference. -/
theorem exchange_change {U V : Matrix ι ι ℚ} (hU : U * U = U) (hUV : U * V = U) :
    exchange U * exchange V = exchange (V - U) := by
  have hsplit : exchange V = exchange U * exchange (V - U) := by
    rw [exchange_mul_of_orthogonal (by rw [mul_sub, hUV, hU, sub_self]), add_sub_cancel]
  rw [hsplit, ← Matrix.mul_assoc, exchange_mul_self hU, Matrix.one_mul]

/-- A coordinate change `R`, applied to both address halves, conjugates `D_U` to the exchange on
the conjugated projector. -/
theorem exchange_conj (R S U : Matrix ι ι ℚ) (h : R * S = 1) :
    fromBlocks R 0 0 R * exchange U * fromBlocks S 0 0 S = exchange (R * U * S) := by
  simp only [exchange, fromBlocks_multiply, mul_sub, sub_mul, mul_one, h, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, sub_self]

/-- A lower triangular projector exchanges its pivot coordinates
after a lower triangular change of basis on each address half. -/
theorem exchange_pivot_coordinates {n : ℕ} (U : Matrix (Fin n) (Fin n) ℚ)
    (lower : U.IsLowerTriangular) (idem : U * U = U) :
    let E := diagonal fun i => U i i
    ∃ C : Matrix (Fin n) (Fin n) ℚ, C.IsLowerTriangular ∧ C⁻¹.IsLowerTriangular ∧
      C * C⁻¹ = 1 ∧ U.rank = Fintype.card {i // U i i ≠ 0} ∧
      fromBlocks C 0 0 C * exchange E * fromBlocks C⁻¹ 0 0 C⁻¹ = exchange U := by
  intro E
  have bits (i) : U i i = 0 ∨ U i i = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℚ => M i i) idem
    change (∑ k, U i k * U k i) = U i i at h
    rw [Finset.sum_eq_single i] at h
    · have hz : U i i * (U i i - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
      exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
    · intro j _ ne
      rcases lt_or_gt_of_ne ne with lt | gt
      · rw [lower (i := j) (j := i) lt, mul_zero]
      · rw [lower (i := i) (j := j) gt, zero_mul]
    · simp
  let C := U * E + (1 - U) * (1 - E)
  have entry (i j) : C i j = U i j * U j j +
      ((1 : Matrix (Fin n) (Fin n) ℚ) i j - U i j) * (1 - U j j) := by
    simp only [C, E, mul_sub, mul_one, Matrix.add_apply, Matrix.sub_apply, mul_diagonal]
  have triangular : C.IsLowerTriangular := by
    intro i j hij
    have h : i < j := hij
    simp [entry, lower hij, one_apply_ne h.ne]
  have diag (i) : C i i = 1 := by
    rcases bits i with h | h <;> simp [entry, h]
  have unit : IsUnit C.det := by simp [C.det_of_isLowerTriangular triangular, diag]
  let := C.invertibleOfIsUnitDet unit
  have eIdem : E * E = E := by
    ext i j
    rw [show E = diagonal (fun i => U i i) from rfl, diagonal_mul_diagonal]
    by_cases h : i = j
    · subst j
      rcases bits i with h | h <;> simp [h]
    · simp [diagonal_apply_ne _ h]
  have intertwine : C * E = U * C := by
    dsimp only [C]
    have hE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, eIdem, sub_self]
    have hU : U * (1 - U) = 0 := by rw [mul_sub, mul_one, idem, sub_self]
    rw [add_mul, Matrix.mul_assoc U E E, eIdem, Matrix.mul_assoc, hE, Matrix.mul_zero,
      mul_add, ← Matrix.mul_assoc, idem, ← Matrix.mul_assoc, hU, Matrix.zero_mul]
  refine ⟨C, triangular, blockTriangular_inv_of_blockTriangular triangular, C.mul_nonsing_inv unit, ?_, ?_⟩
  · have ranks := congrArg Matrix.rank intertwine
    rw [rank_mul_eq_right_of_isUnit_det C E unit, rank_mul_eq_left_of_isUnit_det C U unit] at ranks
    exact ranks.symm.trans (rank_diagonal _)
  rw [exchange_conj _ _ _ (C.mul_nonsing_inv unit), intertwine, Matrix.mul_assoc, C.mul_nonsing_inv unit, mul_one]

/-- Moving between nested triangular frames swaps the coordinates gained by the larger frame. -/
theorem nested_exchange_pivot_coordinates {n : ℕ} (U V : Matrix (Fin n) (Fin n) ℚ)
    (lowerU : U.IsLowerTriangular) (lowerV : V.IsLowerTriangular)
    (idemU : U * U = U) (idemV : V * V = V) (uv : U * V = U) (vu : V * U = U) :
    let E := diagonal fun i => V i i - U i i
    ∃ C : Matrix (Fin n) (Fin n) ℚ, C.IsLowerTriangular ∧ C⁻¹.IsLowerTriangular ∧
      C * C⁻¹ = 1 ∧ (V - U).rank = Fintype.card {i // V i i - U i i ≠ 0} ∧
      fromBlocks C 0 0 C * exchange E * fromBlocks C⁻¹ 0 0 C⁻¹ = exchange U * exchange V := by
  rw [exchange_change idemU uv]
  apply exchange_pivot_coordinates (V - U)
  · intro i j hij
    simp [Matrix.sub_apply, lowerU hij, lowerV hij]
  · rw [sub_mul, mul_sub, mul_sub, idemV, vu, uv, idemU, sub_self, sub_zero]

end Exchange

end IntegerMultBounds.Networks.Certificates.PR589.Nine
