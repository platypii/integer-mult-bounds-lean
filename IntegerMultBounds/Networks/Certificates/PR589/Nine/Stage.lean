module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortFrame

/-!
# The compressed nine-stage window and its stage boundaries

The parent has `m = 64 = 1 + 7·9` axes (`Axis`): the eight local axes of the selected word, then
eight exterior blocks of seven. In upstream's numbering (`axisIndex`) local axis `i` is axis `i`,
and axis `k` of exterior block `b` is axis `8 + 7b + k`.

Stage `0` runs the word on the local axes. Stage `s + 1`, for `s : Fin 8`, runs it on the local
axes and exterior block `s` through the port's route `route s`: `ρ` on those fifteen axes and the
identity on the other exterior blocks. `route_transpose` and `route_mul_self`: the route is a
symmetric involution.

`stageLift n U` is the global frame of the word's local frame `U` at stage `n`: at stage `s + 1`
it is `route s (U ⊕ blocks 0, …, s) route s` (`lift`), and at stage `0` it is `U ⊕ 0`. The frames
of the two sides of a pair after `n` stages are `sourceFrame n` (side zero) and `targetFrame n`
(side one). The stage boundary identities say that the word's frames at stage `n` lift to these:
* `stage_source`, `stage_source_exit`: the word's source frames `P` (initial) and `1` (final) lift
  to `sourceFrame n` and `sourceFrame (n + 1)`;
* `stage_target`, `stage_target_exit`: its target frames `0` and `1 - P` lift to `targetFrame n`
  and `targetFrame (n + 1)`.
So the frame in which a column leaves stage `n` is the frame in which it enters stage `n + 1`.

`lift_sub` is the orthogonal lift argument: the difference of two lifted frames, a lifted MOVE, is
the route conjugate of the local difference, extended by zero. `exchange_lift` is the same for the
bit address operators. `node_exchange_source` and `node_exchange_target`: after nine stages and
the final exchange of sides, each side's frame is its initial frame followed by the full exchange
`D_1` of the two address halves.
-/

@[expose] public section

namespace IntegerMultBounds.Networks.Certificates.PR589.Nine

open Matrix

/-- An exterior axis: a block `b` and an axis `k` within it. -/
abbrev Exterior := Fin 8 × Fin 7

/-- The 64 parent axes: eight local axes and eight exterior blocks of seven. -/
abbrev Axis := Fin 8 ⊕ Exterior

/-- Upstream's axis numbering. -/
def axisIndex : Axis → ℕ
  | .inl i => i.val
  | .inr x => 8 + 7 * x.1.val + x.2.val

theorem axisIndex_lt (a : Axis) : axisIndex a < 64 := by
  rcases a with i | ⟨b, k⟩
  · simp only [axisIndex]; omega
  · simp only [axisIndex]; omega

theorem axisIndex_injective : Function.Injective axisIndex := by
  decide +kernel

/-- The diagonal projector onto the exterior blocks `b < n`. -/
def lower (n : ℕ) : Matrix Exterior Exterior ℚ := diagonal fun x => if x.1.val < n then 1 else 0

/-- The diagonal projector onto exterior block `s`. -/
def block (s : Fin 8) : Matrix Exterior Exterior ℚ := diagonal fun x => if x.1 = s then 1 else 0

/-- The diagonal projector onto the exterior blocks other than `s`. -/
def avoid (s : Fin 8) : Matrix Exterior Exterior ℚ := diagonal fun x => if x.1 = s then 0 else 1

theorem lower_zero : lower 0 = 0 := by
  simp [lower]

theorem lower_eight : lower 8 = 1 := by
  rw [lower, ← diagonal_one]
  congr 1
  funext x
  simp [x.1.isLt]

theorem block_add_lower (s : Fin 8) : block s + lower s.val = lower (s.val + 1) := by
  rw [block, lower, lower, diagonal_add]
  congr 1
  funext x
  by_cases hx : x.1 = s
  · subst hx
    simp
  · have hv : x.1.val ≠ s.val := fun e => hx (Fin.ext e)
    by_cases hl : x.1.val < s.val
    · simp [hx, hl, show x.1.val < s.val + 1 by omega]
    · simp [hx, hl, show ¬x.1.val < s.val + 1 by omega]

theorem block_add_avoid (s : Fin 8) : block s + avoid s = 1 := by
  rw [block, avoid, diagonal_add, ← diagonal_one]
  congr 1
  funext x
  split_ifs <;> simp

theorem avoid_mul_self (s : Fin 8) : avoid s * avoid s = avoid s := by
  rw [avoid, diagonal_mul_diagonal]
  congr 1
  funext x
  split_ifs <;> simp

theorem avoid_mul_lower_mul_avoid (s : Fin 8) : avoid s * lower (s.val + 1) * avoid s = lower s.val := by
  rw [avoid, lower, lower, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  by_cases hx : x.1 = s
  · subst hx
    simp
  · have hv : x.1.val ≠ s.val := fun e => hx (Fin.ext e)
    by_cases hl : x.1.val < s.val
    · simp [hx, hl, show x.1.val < s.val + 1 by omega]
    · simp [hx, hl, show ¬x.1.val < s.val + 1 by omega]

namespace PortCertificate

variable {c : PortCertificate}

/-- The complement columns placed in exterior block `s`. -/
def spread (c : PortCertificate) (s : Fin 8) : Matrix (Fin 8) Exterior ℚ :=
  of fun i x => if x.1 = s then c.complement i x.2 else 0

/-- The route of stage `s + 1`: `ρ` on the local axes and exterior block `s`, the identity on the
other exterior blocks. -/
def route (c : PortCertificate) (s : Fin 8) : Matrix Axis Axis ℚ :=
  fromBlocks c.lineProj (c.spread s) (c.spread s)ᵀ (avoid s)

/-- The global frame at stage `s + 1` of the local frame `U`. -/
def lift (c : PortCertificate) (s : Fin 8) (U : Matrix (Fin 8) (Fin 8) ℚ) : Matrix Axis Axis ℚ :=
  c.route s * fromBlocks U 0 0 (lower (s.val + 1)) * c.route s

/-- The global frame at stage `n` of the local frame `U`. -/
def stageLift (c : PortCertificate) (n : Fin 9) (U : Matrix (Fin 8) (Fin 8) ℚ) :
    Matrix Axis Axis ℚ :=
  if h : n.val = 0 then fromBlocks U 0 0 0 else c.lift ⟨n.val - 1, by omega⟩ U

/-- The frame of a side-zero column after `n` stages. -/
def sourceFrame (c : PortCertificate) : ℕ → Matrix Axis Axis ℚ
  | 0 => fromBlocks c.lineProj 0 0 0
  | n + 1 => fromBlocks 1 0 0 (lower n)

/-- The frame of a side-one column after `n` stages. -/
def targetFrame (c : PortCertificate) : ℕ → Matrix Axis Axis ℚ
  | 0 => 0
  | n + 1 => fromBlocks (1 - c.lineProj) 0 0 (lower n)

theorem lineProj_mul_spread (h : c.Checked) (s : Fin 8) : c.lineProj * c.spread s = 0 := by
  ext i x
  by_cases hx : x.1 = s
  · have hz := congrFun (congrFun (lineProj_mul_complement h) i) x.2
    simpa [mul_apply, spread, hx] using hz
  · simp [mul_apply, spread, hx]

theorem transpose_spread_mul_lineProj (h : c.Checked) (s : Fin 8) :
    (c.spread s)ᵀ * c.lineProj = 0 := by
  have ht := congrArg transpose (lineProj_mul_spread h s)
  rwa [transpose_mul, lineProj_transpose, transpose_zero] at ht

theorem spread_mul_transpose (h : c.Checked) (s : Fin 8) :
    c.spread s * (c.spread s)ᵀ = 1 - c.lineProj := by
  rw [← complement_mul_transpose h]
  ext i j
  simp only [mul_apply, transpose_apply, spread, of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single s]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem transpose_spread_mul_spread (h : c.Checked) (s : Fin 8) :
    (c.spread s)ᵀ * c.spread s = block s := by
  ext x y
  have hc := congrFun (congrFun (complement_orthonormal h) x.2) y.2
  simp only [mul_apply, transpose_apply, one_apply] at hc
  simp only [mul_apply, transpose_apply, spread, of_apply, block, diagonal_apply]
  by_cases hx : x.1 = s
  · by_cases hy : y.1 = s
    · have hxy : x = y ↔ x.2 = y.2 :=
        ⟨fun e => by rw [e], fun e => Prod.ext (hx.trans hy.symm) e⟩
      simp only [hx, hy, ite_true, hc, hxy]
    · have hxy : x ≠ y := fun e => hy (e ▸ hx)
      simp [hx, hy, hxy]
  · simp [hx]

theorem spread_mul_avoid (s : Fin 8) : c.spread s * avoid s = 0 := by
  ext i x
  simp only [avoid, mul_diagonal, spread, of_apply, Matrix.zero_apply]
  split_ifs <;> simp

theorem avoid_mul_transpose_spread (s : Fin 8) : avoid s * (c.spread s)ᵀ = 0 := by
  ext x i
  simp only [avoid, diagonal_mul, transpose_apply, spread, of_apply, Matrix.zero_apply]
  split_ifs <;> simp

theorem spread_mul_lower (s : Fin 8) : c.spread s * lower (s.val + 1) = c.spread s := by
  ext i x
  simp only [lower, mul_diagonal, spread, of_apply]
  by_cases hx : x.1 = s
  · simp [hx]
  · simp [hx]

theorem lower_mul_transpose_spread (s : Fin 8) :
    lower (s.val + 1) * (c.spread s)ᵀ = (c.spread s)ᵀ := by
  ext x i
  simp only [lower, diagonal_mul, transpose_apply, spread, of_apply]
  by_cases hx : x.1 = s
  · simp [hx]
  · simp [hx]

/-- The oblique port route on the full stage window, including the inactive exterior blocks. -/
theorem oblique_stage_route (h : c.Checked) (s : Fin 8) (U : Matrix (Fin 8) (Fin 8) ℚ)
    (up : U * c.lineProj = c.lineProj) (pu : c.lineProj * U = U) :
    let B := (1 - U) * c.spread s
    let R := fromBlocks U B (c.spread s)ᵀ (avoid s)
    let liftFrame := fun X => R * fromBlocks X 0 0 (lower (s.val + 1)) * R
    R * R = 1 ∧ liftFrame U = fromBlocks 1 0 0 (lower s.val) ∧
      liftFrame 1 = fromBlocks 1 0 0 (lower (s.val + 1)) ∧
      liftFrame 0 = fromBlocks (1 - U) 0 0 (lower s.val) ∧
      liftFrame (1 - U) = fromBlocks (1 - U) 0 0 (lower (s.val + 1)) := by
  intro B R liftFrame
  have idem : U * U = U := by calc
    U * U = U * (c.lineProj * U) := by rw [pu]
    _ = U := by rw [← Matrix.mul_assoc, up, pu]
  have annihilate : (c.spread s)ᵀ * U = 0 := by
    calc _ = (c.spread s)ᵀ * (c.lineProj * U) := by rw [pu]
         _ = 0 := by rw [← Matrix.mul_assoc, transpose_spread_mul_lineProj h, Matrix.zero_mul]
  have ub : U * B = 0 := by
    dsimp [B]
    rw [← Matrix.mul_assoc, mul_sub, mul_one, idem, sub_self, Matrix.zero_mul]
  have leftInv : (c.spread s)ᵀ * B = block s := by
    dsimp [B]
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, annihilate, sub_zero,
      transpose_spread_mul_spread h]
  have rightInv : B * (c.spread s)ᵀ = 1 - U := by
    dsimp [B]
    rw [Matrix.mul_assoc, spread_mul_transpose h, mul_sub, mul_one, sub_mul, one_mul,
      up, sub_self, sub_zero]
  have avoidB : B * avoid s = 0 := by simp [B, Matrix.mul_assoc, spread_mul_avoid]
  have lowerB : B * lower (s.val + 1) = B := by simp [B, Matrix.mul_assoc, spread_mul_lower]
  have off : avoid s * lower (s.val + 1) * (c.spread s)ᵀ = 0 := by
    rw [Matrix.mul_assoc, lower_mul_transpose_spread, avoid_mul_transpose_spread]
  simp [liftFrame, R, fromBlocks_multiply, Matrix.mul_sub, idem, ub, annihilate, leftInv,
    rightInv, avoidB, lowerB, off, avoid_mul_transpose_spread, avoid_mul_self,
    avoid_mul_lower_mul_avoid, block_add_lower, block_add_avoid, ← fromBlocks_one]

theorem route_transpose (s : Fin 8) : (c.route s)ᵀ = c.route s := by
  rw [route, fromBlocks_transpose, transpose_transpose, lineProj_transpose, avoid,
    diagonal_transpose]

theorem route_mul_self (h : c.Checked) (s : Fin 8) : c.route s * c.route s = 1 := by
  rw [route, fromBlocks_multiply, lineProj_mul_self h, spread_mul_transpose h,
    lineProj_mul_spread h, spread_mul_avoid, transpose_spread_mul_lineProj h,
    avoid_mul_transpose_spread, transpose_spread_mul_spread h, avoid_mul_self, block_add_avoid,
    ← fromBlocks_one]
  simp

/-- The lifted frame in block form. -/
theorem lift_eq (h : c.Checked) (s : Fin 8) (U : Matrix (Fin 8) (Fin 8) ℚ) :
    c.lift s U =
      fromBlocks (c.lineProj * U * c.lineProj + (1 - c.lineProj)) (c.lineProj * U * c.spread s)
        ((c.spread s)ᵀ * U * c.lineProj) ((c.spread s)ᵀ * U * c.spread s + lower s.val) := by
  have hleft : c.route s * fromBlocks U 0 0 (lower (s.val + 1)) =
      fromBlocks (c.lineProj * U) (c.spread s) ((c.spread s)ᵀ * U) (avoid s * lower (s.val + 1)) := by
    rw [route, fromBlocks_multiply]
    simp [spread_mul_lower]
  rw [lift, hleft, route, fromBlocks_multiply, spread_mul_transpose h, spread_mul_avoid,
    Matrix.mul_assoc (avoid s) (lower (s.val + 1)) (c.spread s)ᵀ, lower_mul_transpose_spread,
    avoid_mul_transpose_spread, avoid_mul_lower_mul_avoid]
  simp

theorem lift_line (h : c.Checked) (s : Fin 8) : c.lift s c.lineProj = c.sourceFrame (s.val + 1) := by
  rw [lift_eq h]
  simp [sourceFrame, lineProj_mul_self h, lineProj_mul_spread h, transpose_spread_mul_lineProj h]

theorem lift_one (h : c.Checked) (s : Fin 8) : c.lift s 1 = c.sourceFrame (s.val + 2) := by
  rw [lift_eq h]
  simp [sourceFrame, lineProj_mul_self h, lineProj_mul_spread h, transpose_spread_mul_lineProj h,
    transpose_spread_mul_spread h, block_add_lower]

theorem lift_zero (h : c.Checked) (s : Fin 8) : c.lift s 0 = c.targetFrame (s.val + 1) := by
  rw [lift_eq h]
  simp [targetFrame]

theorem lift_complement (h : c.Checked) (s : Fin 8) :
    c.lift s (1 - c.lineProj) = c.targetFrame (s.val + 2) := by
  rw [lift_eq h]
  simp [targetFrame, Matrix.mul_sub, lineProj_mul_self h, transpose_spread_mul_lineProj h,
    transpose_spread_mul_spread h, block_add_lower]

/-- The word's initial source frame `P` at stage `n` lifts to the side-zero frame after `n`
stages. -/
theorem stage_source (h : c.Checked) (n : Fin 9) : c.stageLift n c.lineProj = c.sourceFrame n.val := by
  rcases n with ⟨_ | m, hm⟩
  · rfl
  · simp only [stageLift, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
    exact lift_line h ⟨m, by omega⟩

/-- The word's final source frame `1` at stage `n` lifts to the side-zero frame after `n + 1`
stages. -/
theorem stage_source_exit (h : c.Checked) (n : Fin 9) :
    c.stageLift n 1 = c.sourceFrame (n.val + 1) := by
  rcases n with ⟨_ | m, hm⟩
  · simp [stageLift, sourceFrame, lower_zero]
  · simp only [stageLift, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
    exact lift_one h ⟨m, by omega⟩

/-- The word's initial target frame `0` at stage `n` lifts to the side-one frame after `n`
stages. -/
theorem stage_target (h : c.Checked) (n : Fin 9) : c.stageLift n 0 = c.targetFrame n.val := by
  rcases n with ⟨_ | m, hm⟩
  · simp [stageLift, targetFrame]
  · simp only [stageLift, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
    exact lift_zero h ⟨m, by omega⟩

/-- The word's final target frame `1 - P` at stage `n` lifts to the side-one frame after `n + 1`
stages. -/
theorem stage_target_exit (h : c.Checked) (n : Fin 9) :
    c.stageLift n (1 - c.lineProj) = c.targetFrame (n.val + 1) := by
  rcases n with ⟨_ | m, hm⟩
  · simp [stageLift, targetFrame, lower_zero]
  · simp only [stageLift, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]
    exact lift_complement h ⟨m, by omega⟩

/-- A lifted MOVE is the route conjugate of the local one, extended by zero. -/
theorem lift_sub (s : Fin 8) (U V : Matrix (Fin 8) (Fin 8) ℚ) :
    c.lift s V - c.lift s U = c.route s * fromBlocks (V - U) 0 0 0 * c.route s := by
  have hd : fromBlocks V 0 0 (lower (s.val + 1)) - fromBlocks U 0 0 (lower (s.val + 1)) =
      fromBlocks (V - U) (0 : Matrix (Fin 8) Exterior ℚ) 0 0 := by
    ext (i | i) (j | j) <;> simp
  rw [lift, lift, ← Matrix.sub_mul, ← Matrix.mul_sub, hd]

/-- The bit address operator of a lifted frame is the route conjugate of the local one. -/
theorem exchange_lift (h : c.Checked) (s : Fin 8) (U : Matrix (Fin 8) (Fin 8) ℚ) :
    exchange (c.lift s U) =
      fromBlocks (c.route s) 0 0 (c.route s) * exchange (fromBlocks U 0 0 (lower (s.val + 1))) *
        fromBlocks (c.route s) 0 0 (c.route s) :=
  (exchange_conj _ _ _ (route_mul_self h s)).symm

theorem sourceFrame_nine : c.sourceFrame 9 = 1 := by
  simp [sourceFrame, lower_eight, fromBlocks_one]

theorem targetFrame_nine : c.targetFrame 9 = 1 - c.sourceFrame 0 := by
  rw [targetFrame, sourceFrame, lower_eight, ← fromBlocks_one]
  ext (i | i) (j | j) <;> simp [one_apply]

/-- Side zero starts in `sourceFrame 0`; after nine stages the exchange of sides gives it the
side-one frame `targetFrame 9`, which is `D_1` after the initial frame. -/
theorem node_exchange_source :
    exchange (c.targetFrame 9) = exchange 1 * exchange (c.sourceFrame 0) := by
  rw [targetFrame_nine, exchange_one_mul]

/-- Side one starts in `targetFrame 0`; after nine stages the exchange of sides gives it the
side-zero frame `sourceFrame 9`, which is `D_1` after the initial frame. -/
theorem node_exchange_target :
    exchange (c.sourceFrame 9) = exchange 1 * exchange (c.targetFrame 0) := by
  rw [sourceFrame_nine, targetFrame, exchange_zero, Matrix.mul_one]

end PortCertificate

end IntegerMultBounds.Networks.Certificates.PR589.Nine
