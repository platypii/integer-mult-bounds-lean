module

public import IntegerMultBounds.MathlibTM2.M6.PrefixWitnesses.All

/-! Normalized modular generators for the PR589 prefix frames. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix
open IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl

/-- Normalize the selected rows so that their first coordinates form the identity.
The prefix of each original generator then gives its coefficients in the normalized rows. -/
theorem prefix_frame (label : ℕ) (live : label < 636) :
    let d := Geometry.Dimensions.value label
    ∃ (hd : d ≤ 8) (lines : Fin d → Fin 111), (∀ i, (lines i).val ∈ Frames.labels label) ∧
      ∀ w : ℕ, let R := ZMod (prime ^ w)
        let G : Matrix (Fin d) (Fin 8) R := of fun i j => (translatedEntry (lines i) j.val : R)
        let A := G.submatrix id (Fin.castLE hd)
        ∃ B : Matrix (Fin d) (Fin 8) R, B.submatrix id (Fin.castLE hd) = 1 ∧
          A * B = G ∧ B = A⁻¹ * G := by
  intro d
  have bounded : ∀ i : Fin 636, Geometry.Dimensions.value i.val ≤ 8 := by decide +kernel
  have hd : d ≤ 8 := bounded ⟨label, live⟩
  obtain ⟨lines, members, unit⟩ := prefix_witness label live
  refine ⟨hd, lines, members, ?_⟩
  intro w R G A
  have detUnit : IsUnit A.det := (isUnit_iff_isUnit_det A).mp (unit w)
  refine ⟨A⁻¹ * G, ?_, ?_, rfl⟩
  · change A⁻¹ * A = 1
    exact A.nonsing_inv_mul detUnit
  · rw [← Matrix.mul_assoc, A.mul_nonsing_inv detUnit, Matrix.one_mul]

/-- Prefix interpolation is a projection: it fixes every combination of generator
rows, and its output always has the prescribed prefix. -/
theorem prefix_interpolation {R : Type*} [CommRing R] {d : ℕ} (hd : d ≤ 8)
    (G B : Matrix (Fin d) (Fin 8) R) (normalized : B.submatrix id (Fin.castLE hd) = 1)
    (reconstruct : G.submatrix id (Fin.castLE hd) * B = G) :
    let restrict := fun x : Fin 8 → R => x ∘ Fin.castLE hd
    let project := fun x => restrict x ᵥ* B
    (∀ x, restrict (project x) = restrict x) ∧ (∀ x, project (project x) = project x) ∧
      ∀ a, project (a ᵥ* G) = a ᵥ* G := by
  intro restrict project
  have keeps (x) : restrict (project x) = restrict x := by
    change restrict x ᵥ* B.submatrix id (Fin.castLE hd) = restrict x
    rw [normalized, vecMul_one]
  refine ⟨keeps, fun x => congrArg (fun v => v ᵥ* B) (keeps x), ?_⟩
  intro a
  change (a ᵥ* G.submatrix id (Fin.castLE hd)) ᵥ* B = a ᵥ* G
  rw [vecMul_vecMul, reconstruct]

/-- An integral generator relation remains valid on the tape after cancellation of a
unit denominator. Hence the prefix interpolator fixes the additional generator. -/
theorem prefix_fixed_of_scaled_relation {d : ℕ} (hd : d ≤ 8)
    (G : Matrix (Fin d) (Fin 8) ℤ) (x : Fin 8 → ℤ) (a : Fin d → ℤ) (den : ℤ)
    (relation : ∀ j, den * x j = ∑ i, a i * G i j)
    (nz : den ≠ 0) (bound : den.natAbs ≤ 2 ^ 100) (w : ℕ)
    (B : Matrix (Fin d) (Fin 8) (ZMod (prime ^ w)))
    (reconstruct : (G.map (Int.castRingHom (ZMod (prime ^ w)))).submatrix id (Fin.castLE hd) * B =
      G.map (Int.castRingHom (ZMod (prime ^ w)))) :
    (fun i : Fin d => (x (i.castLE hd) : ZMod (prime ^ w))) ᵥ* B =
      fun j => (x j : ZMod (prime ^ w)) := by
  let R := ZMod (prime ^ w)
  let M := G.map (Int.castRingHom R)
  let v (j) : R := x j
  let coeff (i) : R := a i
  have scaled : (den : R) • v = coeff ᵥ* M := by
    funext j
    have h := congrArg (Int.castRingHom R) (relation j)
    simpa [v, coeff, M, vecMul, dotProduct, Pi.smul_apply, smul_eq_mul] using h
  have part : (den : R) • (v ∘ Fin.castLE hd) = coeff ᵥ* M.submatrix id (Fin.castLE hd) :=
    congrArg (fun y : Fin 8 → R => y ∘ Fin.castLE hd) scaled
  have identity : (den : R) • ((v ∘ Fin.castLE hd) ᵥ* B) = (den : R) • v := by
    rw [← smul_vecMul, part, vecMul_vecMul, reconstruct, scaled]
  funext j
  exact (prefix_denominator_unit den nz bound w).mul_right_inj.mp (congrFun identity j)

/-- Cramer's identity clears every rational row relation with the same integer,
the determinant of the prefix minor. -/
theorem prefix_integral_relation {d : ℕ} (hd : d ≤ 8) (G : Matrix (Fin d) (Fin 8) ℤ)
    (x : Fin 8 → ℤ) (a : Fin d → ℚ)
    (span : a ᵥ* G.map (Int.castRingHom ℚ) = fun j => (x j : ℚ)) :
    let A := G.submatrix id (Fin.castLE hd)
    ∃ b : Fin d → ℤ, ∀ j, A.det * x j = ∑ i, b i * G i j := by
  intro A
  let f := Int.castRingHom ℚ
  let u := x ∘ Fin.castLE hd
  let b := u ᵥ* A.adjugate
  have part : a ᵥ* A.map f = f ∘ u :=
    congrArg (fun v : Fin 8 → ℚ => v ∘ Fin.castLE hd) span
  have adj : (A.adjugate.map f) = (A.map f).adjugate := f.map_adjugate A
  have coeff : f ∘ b = (f A.det) • a := by
    calc f ∘ b = (f ∘ u) ᵥ* A.adjugate.map f := funext (f.map_vecMul A.adjugate u)
         _ = _ := by
           rw [← part, adj, vecMul_vecMul, mul_adjugate, vecMul_smul, vecMul_one]
           rw [show (A.map f).det = f A.det from (f.map_det A).symm]
  refine ⟨b, fun j => Int.cast_injective (α := ℚ) ?_⟩
  change f (A.det * x j) = f ((b ᵥ* G) j)
  rw [map_mul, f.map_vecMul, coeff, smul_vecMul, span]
  rfl

/-- Rational span membership suffices to recover a generator over every prime-power
radix. Only the selected prefix determinant enters the denominator bound. -/
theorem prefix_fixed_of_rational_span {d : ℕ} (hd : d ≤ 8) (G : Matrix (Fin d) (Fin 8) ℤ)
    (entries : ∀ i j, (G i j).natAbs ≤ 1344) (x : Fin 8 → ℤ)
    (span : ∃ a : Fin d → ℚ, a ᵥ* G.map (Int.castRingHom ℚ) = fun j => (x j : ℚ))
    (w : ℕ) (B : Matrix (Fin d) (Fin 8) (ZMod (prime ^ w))) :
    let A := G.submatrix id (Fin.castLE hd)
    A.det ≠ 0 → A.map (Int.castRingHom (ZMod (prime ^ w))) * B =
      G.map (Int.castRingHom (ZMod (prime ^ w))) →
    (fun i : Fin d => (x (i.castLE hd) : ZMod (prime ^ w))) ᵥ* B =
      fun j => (x j : ZMod (prime ^ w)) := by
  intro A nz reconstruct
  obtain ⟨a, ha⟩ := span
  obtain ⟨b, relation⟩ := prefix_integral_relation hd G x a ha
  apply prefix_fixed_of_scaled_relation hd G x b A.det relation nz _ w B reconstruct
  exact prefix_det_bound hd A fun i j => entries i (j.castLE hd)

end IntegerMultBounds.MathlibTM2.M6
