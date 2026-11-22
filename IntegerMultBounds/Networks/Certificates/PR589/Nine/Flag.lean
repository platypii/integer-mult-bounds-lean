module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Stage
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Pending coordinates and hosted slots

The orthogonal space of a port's line has the flag basis `flag`: the seven complement columns on
the local axes, then the 56 exterior axes block by block. `pendingIndex` numbers it `0, …, 62`;
upstream's port chart `A_q = diag([q/2 | U_q], I_56)` numbers the same axes `1, …, 63`.
`span x y` is the orthogonal projector onto the flag vectors at positions `x, …, y - 1`.

* The level frames are flag prefixes: `targetFrame_eq` (`targetFrame n = span 0 (7n)`) and
  `sourceFrame_eq` (`sourceFrame n = linePart + span 0 (7n)`). An idle child from `a` to `b`
  stages therefore has the pending projector `span (7a) (7b)` on both sides (`pending_source`,
  `pending_target`).
* `exchange_split` and `exchange_slots`: the exchange on a pending interval is the product of the
  exchanges on consecutive eight-wide slots and on the remainder.
* `slotChart x` is the isometric embedding of a helper's eight local axes onto the slot at position
  `x`: `slotChart_orthonormal` and `slotChart_proj` (`σσᵀ = span x (x + 8)`). A helper's local
  frames `0` and `1` lift to `0` and the slot projector.
* `rank_conj` keeps ranks under an isometric embedding, so a hosted MOVE has the rank of the
  local one (`rank_slot_sub`), and so does a lifted MOVE at every stage (`rank_lift_sub`).
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

open Matrix

/-- A coordinate of the line's orthogonal space: a complement column or an exterior axis. -/
abbrev Pending := Fin 7 ⊕ Exterior

/-- The pending order: the complement columns, then the exterior axes block by block. -/
def pendingIndex : Pending → ℕ
  | .inl k => k.val
  | .inr x => 7 + 7 * x.1.val + x.2.val

theorem pendingIndex_injective : Function.Injective pendingIndex := by
  decide +kernel

/-- The coordinate at a position. -/
def pendingAt (n : Fin 63) : Pending :=
  if h : n.val < 7 then .inl ⟨n.val, h⟩
  else .inr (⟨(n.val - 7) / 7, by omega⟩, ⟨(n.val - 7) % 7, Nat.mod_lt _ (by norm_num)⟩)

theorem pendingIndex_pendingAt : ∀ n : Fin 63, pendingIndex (pendingAt n) = n.val := by
  decide +kernel

/-- The diagonal projector onto the positions `x, …, y - 1`. -/
def interval (x y : ℕ) : Matrix Pending Pending ℚ :=
  diagonal fun p => if x ≤ pendingIndex p ∧ pendingIndex p < y then 1 else 0

theorem interval_add {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    interval x y + interval y z = interval x z := by
  rw [interval, interval, interval, diagonal_add]
  congr 1
  funext p
  by_cases h1 : pendingIndex p < y
  · by_cases h0 : x ≤ pendingIndex p
    · simp [h0, h1, show ¬y ≤ pendingIndex p by omega, show pendingIndex p < z by omega]
    · simp [h0, h1]
  · simp [h1, show x ≤ pendingIndex p by omega, show y ≤ pendingIndex p by omega]

theorem interval_mul_disjoint {x y x' y' : ℕ} (hy : y ≤ x') : interval x y * interval x' y' = 0 := by
  rw [interval, interval, diagonal_mul_diagonal, ← diagonal_zero]
  congr 1
  funext p
  by_cases h : pendingIndex p < y
  · simp [h, show ¬x' ≤ pendingIndex p by omega]
  · simp [h]

theorem interval_mul_self (x y : ℕ) : interval x y * interval x y = interval x y := by
  rw [interval, diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp

namespace PortCertificate

variable {c : PortCertificate}

/-- The flag basis of the line's orthogonal space. -/
def flag (c : PortCertificate) : Matrix Axis Pending ℚ := fromBlocks c.complement 0 0 1

/-- The line projector on the parent axes. -/
def linePart (c : PortCertificate) : Matrix Axis Axis ℚ := fromBlocks c.lineProj 0 0 0

/-- The orthogonal projector onto the flag vectors at positions `x, …, y - 1`. -/
def span (c : PortCertificate) (x y : ℕ) : Matrix Axis Axis ℚ := c.flag * interval x y * c.flagᵀ

theorem flag_orthonormal (h : c.Checked) : c.flagᵀ * c.flag = 1 := by
  rw [flag, fromBlocks_transpose, fromBlocks_multiply, complement_orthonormal h, ← fromBlocks_one]
  simp

theorem flag_mul_transpose (h : c.Checked) : c.flag * c.flagᵀ = 1 - c.linePart := by
  rw [flag, fromBlocks_transpose, fromBlocks_multiply, complement_mul_transpose h, linePart]
  ext (i | i) (j | j) <;> simp [one_apply]

theorem span_add {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    c.span x y + c.span y z = c.span x z := by
  rw [span, span, span, ← Matrix.add_mul, ← Matrix.mul_add, interval_add hxy hyz]

theorem span_mul (h : c.Checked) (x y x' y' : ℕ) :
    c.span x y * c.span x' y' = c.flag * (interval x y * interval x' y') * c.flagᵀ := by
  rw [span, span, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc c.flagᵀ,
    ← Matrix.mul_assoc c.flagᵀ, flag_orthonormal h, Matrix.one_mul, Matrix.mul_assoc,
    Matrix.mul_assoc]

theorem span_mul_disjoint (h : c.Checked) {x y x' y' : ℕ} (hy : y ≤ x') :
    c.span x y * c.span x' y' = 0 := by
  rw [span_mul h, interval_mul_disjoint hy, Matrix.mul_zero, Matrix.zero_mul]

theorem span_mul_self (h : c.Checked) (x y : ℕ) : c.span x y * c.span x y = c.span x y := by
  rw [span_mul h, interval_mul_self, span]

theorem span_zero_zero : c.span 0 0 = 0 := by
  have : interval 0 0 = 0 := by
    rw [interval, ← diagonal_zero]
    congr 1
  rw [span, this, Matrix.mul_zero, Matrix.zero_mul]

/-- Beyond the seven complement columns the port flag is the parent exterior
basis, so an interval exchange there needs no port-dependent chart. -/
theorem span_exterior (lo hi : ℕ) (outside : 7 ≤ lo) :
    c.span lo hi = fromBlocks 0 0 0 (diagonal fun k : Exterior =>
      if lo ≤ pendingIndex (.inr k) ∧ pendingIndex (.inr k) < hi then (1 : ℚ) else 0) := by
  let E := diagonal fun k : Exterior =>
    if lo ≤ pendingIndex (.inr k) ∧ pendingIndex (.inr k) < hi then (1 : ℚ) else 0
  have coords : interval lo hi = fromBlocks 0 0 0 E := by
    ext (i | i) (j | j)
    · have skip : ¬lo ≤ i.val := by omega
      simp [interval, diagonal_apply, pendingIndex, skip]
    · simp [interval]
    · simp [interval]
    · simp [interval, E, diagonal_apply]
  rw [span, coords, flag, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [E]

/-- Parent addresses have eight local digits, one more than the pending
prefix. Both endpoints of an exterior child therefore shift by one. -/
theorem span_exterior_parent (lo hi : ℕ) (outside : 7 ≤ lo) :
    c.span lo hi = diagonal fun a => if lo+1 ≤ axisIndex a ∧ axisIndex a < hi+1
      then (1 : ℚ) else 0 := by
  rw [span_exterior lo hi outside]
  ext (i | i) (j | j)
  · have skip : ¬lo < i.val := by omega
    simp [diagonal_apply, axisIndex, skip]
  · simp
  · simp
  · have shift : axisIndex (.inr i) = pendingIndex (.inr i)+1 := by
      simp only [axisIndex, pendingIndex]; omega
    simp [diagonal_apply, shift]

/-- The flag prefix of `7(n + 1)` positions is the side-one frame after `n + 1` stages. -/
theorem span_prefix (h : c.Checked) (n : ℕ) :
    c.span 0 (7 * (n + 1)) = fromBlocks (1 - c.lineProj) 0 0 (lower n) := by
  have hint : interval 0 (7 * (n + 1)) = fromBlocks 1 0 0 (lower n) := by
    ext (k | k) (l | l)
    · simp only [interval, diagonal_apply, fromBlocks_apply₁₁, one_apply, Sum.inl.injEq,
        pendingIndex]
      split_ifs <;> simp_all
      omega
    · simp [interval]
    · simp [interval]
    · simp only [interval, diagonal_apply, fromBlocks_apply₂₂, lower, Sum.inr.injEq,
        pendingIndex]
      by_cases hkl : k = l
      · subst hkl
        have : k.2.val < 7 := k.2.isLt
        by_cases hb : k.1.val < n
        · simp [hb, show 7 + 7 * k.1.val + k.2.val < 7 * (n + 1) by omega]
        · simp [hb, show ¬7 + 7 * k.1.val + k.2.val < 7 * (n + 1) by omega]
      · simp [hkl]
  rw [span, hint, flag, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add,
    transpose_zero, transpose_one, complement_mul_transpose h]

/-- The side-one frame after `n` stages is the flag prefix of `7n` positions. -/
theorem targetFrame_eq (h : c.Checked) (n : ℕ) : c.targetFrame n = c.span 0 (7 * n) := by
  cases n with
  | zero => rw [targetFrame, Nat.mul_zero, span_zero_zero]
  | succ n => rw [targetFrame, span_prefix h]

/-- The side-zero frame after `n` stages is the line plus the flag prefix of `7n` positions. -/
theorem sourceFrame_eq (h : c.Checked) (n : ℕ) :
    c.sourceFrame n = c.linePart + c.span 0 (7 * n) := by
  cases n with
  | zero => rw [sourceFrame, Nat.mul_zero, span_zero_zero, add_zero, linePart]
  | succ n =>
    rw [sourceFrame, span_prefix h, linePart, fromBlocks_add]
    simp

/-- An idle advance from `a` to `b` stages has the pending projector `span (7a) (7b)` on side
zero. -/
theorem pending_source (h : c.Checked) {a b : ℕ} (hab : a ≤ b) :
    c.sourceFrame b - c.sourceFrame a = c.span (7 * a) (7 * b) := by
  rw [sourceFrame_eq h, sourceFrame_eq h, ← span_add (Nat.zero_le _) (by omega : 7 * a ≤ 7 * b)]
  abel

/-- The same pending projector on side one. -/
theorem pending_target (h : c.Checked) {a b : ℕ} (hab : a ≤ b) :
    c.targetFrame b - c.targetFrame a = c.span (7 * a) (7 * b) := by
  rw [targetFrame_eq h, targetFrame_eq h, ← span_add (Nat.zero_le _) (by omega : 7 * a ≤ 7 * b)]
  abel

/-- The exchange on an interval splits at any interior position. -/
theorem exchange_split (h : c.Checked) {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) :
    exchange (c.span x z) = exchange (c.span x y) * exchange (c.span y z) := by
  rw [exchange_mul_of_orthogonal (span_mul_disjoint h le_rfl), span_add hxy hyz]

/-- The exchange on a pending interval is the product of the exchanges on `k` consecutive
eight-wide slots and on the remainder. -/
theorem exchange_slots (h : c.Checked) (x k z : ℕ) (hk : x + 8 * k ≤ z) :
    exchange (c.span x z) =
      ((List.range k).map fun j => exchange (c.span (x + 8 * j) (x + 8 * j + 8))).prod *
        exchange (c.span (x + 8 * k) z) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih (by omega), exchange_split h (by omega : x + 8 * k ≤ x + 8 * k + 8)
      (by omega : x + 8 * k + 8 ≤ z), List.range_succ, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, Matrix.mul_assoc,
      show x + 8 * (k + 1) = x + 8 * k + 8 by ring]

/-! ### Slot charts -/

/-- The selection of the eight positions `x, …, x + 7`. -/
def pick (x : ℕ) : Matrix Pending (Fin 8) ℚ :=
  of fun p j => if pendingIndex p = x + j.val then 1 else 0

theorem pick_orthonormal {x : ℕ} (hx : x + 8 ≤ 63) : (pick x)ᵀ * pick x = 1 := by
  ext j l
  simp only [mul_apply, transpose_apply, pick, of_apply, one_apply]
  rw [Fintype.sum_eq_single (pendingAt ⟨x + j.val, by omega⟩)]
  · rw [pendingIndex_pendingAt]
    by_cases hjl : j = l
    · simp [hjl]
    · have : (j : ℕ) ≠ l := fun e => hjl (Fin.ext e)
      simp [hjl, this]
  · intro p hp
    have hne : pendingIndex p ≠ x + j.val := by
      intro e
      apply hp
      apply pendingIndex_injective
      rw [pendingIndex_pendingAt]
      exact e
    simp [hne]

theorem pick_mul_transpose (x : ℕ) : pick x * (pick x)ᵀ = interval x (x + 8) := by
  ext p p'
  simp only [mul_apply, transpose_apply, pick, of_apply, interval, diagonal_apply]
  by_cases hin : x ≤ pendingIndex p ∧ pendingIndex p < x + 8
  · rw [Finset.sum_eq_single ⟨pendingIndex p - x, by omega⟩]
    · by_cases hpp : p = p'
      · subst hpp
        simp [hin, show x + (pendingIndex p - x) = pendingIndex p by omega]
      · have hne : pendingIndex p' ≠ pendingIndex p := fun e => hpp (pendingIndex_injective e.symm)
        simp [hpp, show x + (pendingIndex p - x) = pendingIndex p by omega, hne]
    · intro j _ hj
      have : pendingIndex p ≠ x + j.val := fun e => hj (Fin.ext (by simp; omega))
      simp [this]
    · simp
  · rw [Finset.sum_eq_zero]
    · simp [hin]
    · intro j _
      have : pendingIndex p ≠ x + j.val := fun e => hin ⟨by omega, by omega⟩
      simp [this]

/-- The isometric embedding of a helper's eight local axes onto the slot at position `x`. -/
def slotChart (c : PortCertificate) (x : ℕ) : Matrix Axis (Fin 8) ℚ := c.flag * pick x

theorem slotChart_orthonormal (h : c.Checked) {x : ℕ} (hx : x + 8 ≤ 63) :
    (c.slotChart x)ᵀ * c.slotChart x = 1 := by
  rw [slotChart, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc c.flagᵀ, flag_orthonormal h,
    Matrix.one_mul, pick_orthonormal hx]

theorem slotChart_proj (x : ℕ) : c.slotChart x * (c.slotChart x)ᵀ = c.span x (x + 8) := by
  rw [slotChart, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (pick x), pick_mul_transpose,
    ← Matrix.mul_assoc, span]

/-- A helper's initial frame `0` lifts to zero. -/
theorem slot_lift_zero (x : ℕ) :
    c.slotChart x * (0 : Matrix (Fin 8) (Fin 8) ℚ) * (c.slotChart x)ᵀ = 0 := by
  simp

/-- A helper's final frame `1` lifts to the slot projector. -/
theorem slot_lift_one (x : ℕ) :
    c.slotChart x * (1 : Matrix (Fin 8) (Fin 8) ℚ) * (c.slotChart x)ᵀ = c.span x (x + 8) := by
  rw [Matrix.mul_one, slotChart_proj]

end PortCertificate

/-! ### Ranks -/

/-- Conjugating by an isometric embedding keeps the rank. -/
theorem rank_conj {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] (σ : Matrix m n ℚ)
    (hσ : σᵀ * σ = 1) (M : Matrix n n ℚ) : (σ * M * σᵀ).rank = M.rank := by
  apply le_antisymm
  · exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
  · have hM : M = σᵀ * (σ * M * σᵀ) * σ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hσ, Matrix.one_mul, Matrix.mul_assoc, hσ,
        Matrix.mul_one]
    calc M.rank = (σᵀ * (σ * M * σᵀ) * σ).rank := by rw [← hM]
      _ ≤ (σ * M * σᵀ).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)

namespace PortCertificate

variable {c : PortCertificate}

/-- A hosted MOVE between the helper's local frames `U` and `V` has the local rank. -/
theorem rank_slot_sub (h : c.Checked) {x : ℕ} (hx : x + 8 ≤ 63) (U V : Matrix (Fin 8) (Fin 8) ℚ) :
    (c.slotChart x * V * (c.slotChart x)ᵀ - c.slotChart x * U * (c.slotChart x)ᵀ).rank =
      (V - U).rank := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, rank_conj _ (slotChart_orthonormal h hx)]

/-- The embedding of the local axes into the parent axes. -/
def localChart : Matrix Axis (Fin 8) ℚ :=
  of fun a j => Sum.elim (fun i => if i = j then (1 : ℚ) else 0) (fun _ => 0) a

theorem localChart_orthonormal : localChartᵀ * localChart = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [localChart, mul_apply, Fintype.sum_sum_type]
  · simp [localChart, mul_apply, Fintype.sum_sum_type, hij, Ne.symm hij]

theorem localChart_conj (M : Matrix (Fin 8) (Fin 8) ℚ) :
    localChart * M * localChartᵀ = fromBlocks M 0 0 0 := by
  ext (i | i) (j | j) <;> simp [localChart, mul_apply]

/-- A lifted MOVE at stage `s + 1` has the rank of the local one. -/
theorem rank_lift_sub (h : c.Checked) (s : Fin 8) (U V : Matrix (Fin 8) (Fin 8) ℚ) :
    (c.lift s V - c.lift s U).rank = (V - U).rank := by
  have hσ : (c.route s * localChart)ᵀ * (c.route s * localChart) = 1 := by
    simp only [transpose_mul, route_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (c.route s) (c.route s), route_mul_self h, Matrix.one_mul,
      localChart_orthonormal]
  have he : c.lift s V - c.lift s U =
      c.route s * localChart * (V - U) * (c.route s * localChart)ᵀ := by
    rw [lift_sub, transpose_mul, route_transpose, ← localChart_conj]
    simp only [Matrix.mul_assoc]
  rw [he, rank_conj _ hσ]

end PortCertificate

end IntegerMultBounds.Networks.Certificates.PR589.Nine
