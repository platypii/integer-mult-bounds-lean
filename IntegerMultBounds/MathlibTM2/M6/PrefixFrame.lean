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

end IntegerMultBounds.MathlibTM2.M6
