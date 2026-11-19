module

public import IntegerMultBounds.MathlibTM2.M6.PortSwap
public import IntegerMultBounds.MathlibTM2.M8.Exchange

/-! Folding a simultaneous port permutation into already scheduled endpoint interchanges. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open IntegerMultBounds.Swap.Shear (Op State run interchanges)
open M8.Exchange (transform)

/-- Crossing the partners of two endpoint interchanges performs the ordinary
two interchanges followed by the port permutation on both address halves. -/
theorem crossed_port_swaps {R : Type*} [CommRing R] (s : State (Fin 8) R) :
    run [.interchange 0 7, .interchange 7 0] s =
      transform portSwap portSwap (run [.interchange 0 0, .interchange 7 7] s) := by
  apply Prod.ext <;> funext k <;>
    simp only [transform, portSwap_mulVec, IntegerMultBounds.Swap.Shear.run_cons,
      IntegerMultBounds.Swap.Shear.run_nil, Op.run] <;>
    fin_cases k <;> simp [Equiv.swap_apply_def, Function.update]

/-- An intervening program can stay in place when it commutes with the first
endpoint interchange in both partner assignments. Thus the two credited swaps
need not be consecutive. -/
theorem crossed_port_window {R : Type*} [CommRing R] (mid : List (Op (Fin 8) R))
    (commutes : ∀ j ∈ ([0, 7] : List (Fin 8)), ∀ s : State (Fin 8) R,
      run mid ((Op.interchange 0 j).run s) = (Op.interchange 0 j).run (run mid s))
    (s : State (Fin 8) R) :
    run (.interchange 0 7 :: mid ++ [.interchange 7 0]) s =
      transform portSwap portSwap (run (.interchange 0 0 :: mid ++ [.interchange 7 7]) s) := by
  simp only [IntegerMultBounds.Swap.Shear.run_cons, IntegerMultBounds.Swap.Shear.run_append,
    commutes 7 (by decide), commutes 0 (by decide)]
  exact crossed_port_swaps (run mid s)

theorem crossed_port_window_count {R : Type*} (mid : List (Op (Fin 8) R)) :
    interchanges (.interchange 0 7 :: mid ++ [.interchange 7 0]) = interchanges mid + 2 := by
  change interchanges ([.interchange 0 7] ++ (mid ++ [.interchange 7 0])) = _
  simp only [IntegerMultBounds.Swap.Shear.interchanges_append]
  change 1 + (interchanges mid + 1) = _
  omega

/-- For a dimension-one to dimension-seven MOVE, the six exchanged positions
are exactly the interior of each half. Adding the port swap moves all sixteen
positions; no single plain six-atom block exchange has that action. -/
theorem interior_move_with_port_swap :
    let move := Routing.blockExchange 1 9 6
    let port := fun k => Routing.blockExchange 8 15 1 (Routing.blockExchange 0 7 1 k)
    ∀ a b : Fin 16, a.val + 6 ≤ b.val → b.val + 6 ≤ 16 →
      ∃ k : Fin 16, Routing.blockExchange a.val b.val 6 k.val ≠ port (move k.val) := by
  decide +kernel

open Matrix

def addressMatrix {R : Type*} [CommRing R] (p : Fin 16 → ℕ) : Matrix (Fin 16) (Fin 16) R :=
  of fun i j => if j.val = p i then 1 else 0

/-- Lower triangular passes can only carry an entry upward in column index if
some earlier row of the intervening permutation already reaches that column. -/
private theorem prefix_reach {R : Type*} [CommRing R] [Nontrivial R]
    (p q : Fin 16 → ℕ) (bound : ∀ i, q i < 16) (A B : Matrix (Fin 16) (Fin 16) R)
    (la : A.IsLowerTriangular) (lb : B.IsLowerTriangular)
    (eq : A * addressMatrix (R := R) p * B = addressMatrix (R := R) q) (i : Fin 16) :
    ∃ k ≤ i, q i ≤ p k := by
  classical
  by_contra! none
  let j : Fin 16 := ⟨q i, bound i⟩
  have zero : (A * (addressMatrix (R := R) p * B)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases h : k ≤ i
    · have inner : (addressMatrix (R := R) p * B) k j = 0 := by
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro l _
        by_cases hit : l.val = p k
        · have lt : l < j := hit.trans_lt (none k h)
          rw [lb (i := l) (j := j) lt, mul_zero]
        · simp [addressMatrix, hit]
      rw [inner, mul_zero]
    · rw [la (i := i) (j := k) (lt_of_not_ge h), zero_mul]
  rw [← Matrix.mul_assoc, eq] at zero
  simp [addressMatrix, j] at zero

/-- Even invertible triangular passes around one width-six or width-seven child cannot realize
the MOVE ending at coordinate seven with an endpoint swap in both halves, in the flat address order. -/
theorem interior_move_triangular_obstruction {R : Type*} [CommRing R] [Nontrivial R]
    (n : Fin 2) (a b : Fin 16) (sep : a.val + (6 + n.val) ≤ b.val) (bound : b.val + (6 + n.val) ≤ 16)
    (A B : Matrix (Fin 16) (Fin 16) R) (la : A.IsLowerTriangular) (lb : B.IsLowerTriangular)
    (ua : IsUnit A) (ub : IsUnit B) :
    let p := fun i : Fin 16 => Routing.blockExchange a.val b.val (6 + n.val) i.val
    let q := fun i : Fin 16 => Routing.blockExchange (1 - n.val) (9 - n.val) (6 + n.val)
      (Routing.blockExchange 8 15 1 (Routing.blockExchange 0 7 1 i.val))
    A * addressMatrix (R := R) p * B ≠ addressMatrix (R := R) q := by
  intro p q eq
  have pb (i : Fin 16) := Routing.blockExchange_lt 16 a.val b.val (6 + n.val) i.val sep bound i.isLt
  have qb : ∀ i, q i < 16 := by fin_cases n <;> decide
  have fwd := prefix_reach p q qb A B la lb eq
  have da := (Matrix.isUnit_iff_isUnit_det _).mp ua
  have db := (Matrix.isUnit_iff_isUnit_det _).mp ub
  let := A.invertibleOfIsUnitDet da
  let := B.invertibleOfIsUnitDet db
  have rev : A⁻¹ * addressMatrix (R := R) q * B⁻¹ = addressMatrix (R := R) p := by
    rw [← eq, ← Matrix.mul_assoc, ← Matrix.mul_assoc, A.nonsing_inv_mul da,
      Matrix.one_mul, Matrix.mul_assoc, B.mul_nonsing_inv db, Matrix.mul_one]
  have back := prefix_reach q p pb _ _ (blockTriangular_inv_of_blockTriangular la)
    (blockTriangular_inv_of_blockTriangular lb) rev
  have exclude : ∀ x y : Fin 16, x.val + (6 + n.val) ≤ y.val → y.val + (6 + n.val) ≤ 16 →
      let u := fun i : Fin 16 => Routing.blockExchange x.val y.val (6 + n.val) i.val
      ¬ ((∃ k ≤ (0 : Fin 16), q 0 ≤ u k) ∧ (∃ k ≤ (0 : Fin 16), u 0 ≤ q k) ∧
        (∃ k ≤ (8 : Fin 16), q 8 ≤ u k)) := by fin_cases n <;> decide +kernel
  exact exclude a b sep bound ⟨fwd 0, back 0, fwd 8⟩

end IntegerMultBounds.MathlibTM2.M6
