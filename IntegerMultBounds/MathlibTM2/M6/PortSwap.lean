module

public import IntegerMultBounds.MathlibTM2.Routing.BlockExchange
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortFrame

/-! Reconciling the complement of a prefix line with a prefix hyperplane at a port. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks.Certificates.PR589.Nine

/-- Swapping just the endpoints moves the trailing seven positions to the leading seven. -/
def portSwap {R : Type*} [CommRing R] : Matrix (Fin 8) (Fin 8) R :=
  of fun i j => if j = Equiv.swap (0 : Fin 8) 7 i then 1 else 0

theorem portSwap_isUnit {R : Type*} [CommRing R] : IsUnit (portSwap (R := R)) := by
  have inverse : (portSwap : Matrix (Fin 8) (Fin 8) R) * portSwapᵀ = 1 := by
    ext i j
    simp [Matrix.mul_apply, portSwap, Matrix.one_apply, eq_comm]
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse inverse)

/-- In a packed address this port permutation is one exchange of two atoms of
width `w`, at any base offset. Every bit within an atom keeps its offset. -/
theorem portSwap_blockExchange (base w : ℕ) (k : Fin 8) (r : ℕ) (hr : r < w) :
    Routing.blockExchange base (base + 7 * w) w (base + k.val * w + r) =
      base + (Equiv.swap (0 : Fin 8) 7 k).val * w + r := by
  fin_cases k <;> simp [Routing.blockExchange, Equiv.swap_apply_def] <;> (try split_ifs) <;> omega

theorem portSwap_mulVec {R : Type*} [CommRing R] (x : Fin 8 → R) (i : Fin 8) :
    (portSwap *ᵥ x) i = x (Equiv.swap 0 7 i) := by
  simp [portSwap, mulVec, dotProduct]

private theorem swap_complement {R : Type*} [CommRing R] :
    let L : Matrix (Fin 8) (Fin 8) R := diagonal fun i => if i.val < 1 then 1 else 0
    let H : Matrix (Fin 8) (Fin 8) R := diagonal fun i => if i.val < 7 then 1 else 0
    portSwap * (1 - L) = H * portSwap := by
  intro L H
  ext i j
  simp only [L, H, mul_sub, mul_one, Matrix.sub_apply, mul_diagonal, diagonal_mul, portSwap, of_apply]
  have h : ∀ k : Fin 8, (Equiv.swap (0 : Fin 8) 7 k).val < 1 ↔ ¬ k.val < 7 := by decide
  by_cases eq : j = Equiv.swap (0 : Fin 8) 7 i
  · subst j
    by_cases hi : i.val < 7 <;> simp [h, hi]
  · simp [eq]

/-- The port permutation cannot be absorbed into lower triangular passes on an
isolated address half. The first row of any triangular intertwiner would vanish. -/
theorem port_route_not_triangular {R : Type*} [CommRing R] [Nontrivial R]
    (L H G : Matrix (Fin 8) (Fin 8) R) (lowerH : H.IsLowerTriangular)
    (line : L 0 0 = 1) (hyper : H 0 0 = 1) (unit : IsUnit G)
    (route : G * (1 - L) = H * G) : ¬ G.IsLowerTriangular := by
  intro lowerG
  have row (A : Matrix (Fin 8) (Fin 8) R) (tri : A.IsLowerTriangular)
      (B : Matrix (Fin 8) (Fin 8) R) : (A * B) 0 0 = A 0 0 * B 0 0 := by
    rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · intro k _ hk
      have pos : (0 : Fin 8) < k := Fin.pos_iff_ne_zero.mpr hk
      rw [tri (i := 0) (j := k) pos, zero_mul]
    · simp
  have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) R => M 0 0) route
  simp only [row G lowerG, row H lowerH, Matrix.sub_apply, Matrix.one_apply_eq, line,
    hyper, sub_self, mul_zero, one_mul] at h
  have detZero : G.det = 0 := by
    rw [G.det_of_isLowerTriangular lowerG]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) h.symm
  exact ((Matrix.isUnit_iff_isUnit_det _).mp unit).ne_zero detZero

/-- For any modular line and hyperplane with the certified prefix pivots, triangular
basis changes on either side of the same endpoint swap reconcile the two port frames. -/
theorem port_complement_route {R : Type*} [CommRing R] (L H : Matrix (Fin 8) (Fin 8) R)
    (ltL : L.IsLowerTriangular) (ltH : H.IsLowerTriangular)
    (idemL : L * L = L) (idemH : H * H = H)
    (line : ∀ i : Fin 8, L i i = if i.val < 1 then 1 else 0)
    (hyper : ∀ i : Fin 8, H i i = if i.val < 7 then 1 else 0) :
    ∃ A B : Matrix (Fin 8) (Fin 8) R, A.IsLowerTriangular ∧ B.IsLowerTriangular ∧
      IsUnit A ∧ IsUnit B ∧ (B * portSwap * A) * (1 - L) = H * (B * portSwap * A) := by
  obtain ⟨C, tri, _, unit, lc, _⟩ := triangular_projector_basis L ltL idemL
    (fun i => by rw [line]; split <;> simp)
  obtain ⟨B, tb, _, ub, hb, _⟩ := triangular_projector_basis H ltH idemH
    (fun i => by rw [hyper]; split <;> simp)
  let := C.invertibleOfIsUnitDet unit
  rw [funext line] at lc
  rw [funext hyper] at hb
  have inv := C.mul_nonsing_inv unit
  have inv' := C.nonsing_inv_mul unit
  have il := congrArg (fun M => C⁻¹ * M * C⁻¹) lc
  simp only [← Matrix.mul_assoc, inv', Matrix.one_mul] at il
  rw [Matrix.mul_assoc (C⁻¹ * L), inv, Matrix.mul_one] at il
  refine ⟨C⁻¹, B, blockTriangular_inv_of_blockTriangular tri, tb,
    Matrix.isUnit_nonsing_inv_iff.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr unit),
    (Matrix.isUnit_iff_isUnit_det _).mpr ub, ?_⟩
  have complement := swap_complement (R := R)
  simp only [mul_sub, mul_one] at complement
  simp only [mul_sub, mul_one, Matrix.mul_assoc]
  rw [← il, ← Matrix.mul_assoc portSwap, ← mul_sub, ← sub_mul, complement]
  rw [← Matrix.mul_assoc H B, ← hb]
  simp only [Matrix.mul_assoc]

end IntegerMultBounds.MathlibTM2.M6
