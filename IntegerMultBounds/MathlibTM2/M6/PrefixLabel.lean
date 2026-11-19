module

public import IntegerMultBounds.MathlibTM2.M6.PrefixFrame
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Dimensions.All

/-! The modular prefix projection fixes the entire translated PR589 label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl

private def translate : Geometry.Address →ₗ[ℚ] Geometry.Address :=
  (Matrix.of fun (j k : Fin 8) => (k.val.choose j.val : ℚ) * 2 ^ (k.val - j.val)).mulVecLin

private theorem translate_root (line : Fin 111) :
    translate (Geometry.root line.val) = fun j => (translatedEntry line j.val : ℚ) := by
  have check : ∀ l : Fin 111, ∀ j : Fin 8,
      translate (Geometry.root l.val) j = (translatedEntry l j.val : ℚ) := by decide +kernel
  exact funext (check line)

/-- Every generator of a label is a rational combination of any full set of its
generators with nonsingular translated prefix. -/
theorem translated_label_span {label d : ℕ} (hd : d ≤ 8)
    (dimension : Module.finrank ℚ (Geometry.label label) = d) (lines : Fin d → Fin 111)
    (members : ∀ i, (lines i).val ∈ Frames.labels label) :
    let G : Matrix (Fin d) (Fin 8) ℤ := of fun i j => translatedEntry (lines i) j.val
    let A := G.submatrix id (Fin.castLE hd)
    A.det ≠ 0 → ∀ line : Fin 111, line.val ∈ Frames.labels label →
      ∃ a : Fin d → ℚ, a ᵥ* G.map (Int.castRingHom ℚ) = fun j => (translatedEntry line j.val : ℚ) := by
  intro G A nz line member
  let row := fun i => translate (Geometry.root (lines i).val)
  have ratDet : (A.map (Int.castRingHom ℚ)).det ≠ 0 := by
    change ((Int.castRingHom ℚ).mapMatrix A).det ≠ 0
    rw [← RingHom.map_det]
    change (A.det : ℚ) ≠ 0
    exact_mod_cast nz
  let restrict : Geometry.Address →ₗ[ℚ] (Fin d → ℚ) :=
    LinearMap.pi fun i => LinearMap.proj (R := ℚ) (i.castLE hd)
  have indep : LinearIndependent ℚ row := by
    apply LinearIndependent.of_comp restrict
    have eq : restrict ∘ row = (A.map (Int.castRingHom ℚ)).row := by
      funext i j
      exact congrFun (translate_root (lines i)) (j.castLE hd)
    rw [eq]
    exact linearIndependent_rows_of_det_ne_zero ratDet
  have sub : Submodule.span ℚ (Set.range row) ≤ (Geometry.label label).map translate := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨_, Geometry.root_mem _ _ (members i), rfl⟩
  have equal := Submodule.eq_of_le_of_finrank_le sub (by
    rw [finrank_span_eq_card indep, Fintype.card_fin, ← dimension]
    exact Submodule.finrank_map_le _ _)
  have mem : translate (Geometry.root line.val) ∈ Submodule.span ℚ (Set.range row) :=
    equal ▸ ⟨_, Geometry.root_mem _ _ member, rfl⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp mem
  refine ⟨a, ?_⟩
  funext j
  simpa [row, translate_root, Finset.sum_apply, vecMul, dotProduct, G] using congrFun ha j

/-- Every translated generator listed for the label is reconstructed from its
dimension-many prefix coordinates over every tape radix. -/
theorem label_interpolation (label : ℕ) (live : label < 636) :
    let d := Geometry.Dimensions.value label
    ∃ hd : d ≤ 8, ∀ w : ℕ, let R := ZMod (prime ^ w)
      ∃ B : Matrix (Fin d) (Fin 8) R, B.submatrix id (Fin.castLE hd) = 1 ∧
        ∀ line : Fin 111, line.val ∈ Frames.labels label →
          (fun i : Fin d => (translatedEntry line i.val : R)) ᵥ* B =
            fun j => (translatedEntry line j.val : R) := by
  intro d
  have bounded : ∀ i : Fin 636, Geometry.Dimensions.value i.val ≤ 8 := by decide +kernel
  let hd : d ≤ 8 := bounded ⟨label, live⟩
  obtain ⟨lines, members, units⟩ := prefix_witness label live
  let G : Matrix (Fin d) (Fin 8) ℤ := of fun i j => translatedEntry (lines i) j.val
  let A := G.submatrix id (Fin.castLE hd)
  have nz : A.det ≠ 0 := by
    let : Fact prime.Prime := ⟨prime_prime⟩
    have unit : IsUnit ((Int.castRingHom (ZMod prime)).mapMatrix A) := by
      have h : IsUnit ((Int.castRingHom (ZMod (prime ^ 1))).mapMatrix A) := units 1
      rwa [pow_one] at h
    have h := (isUnit_iff_isUnit_det _).mp unit
    rw [← RingHom.map_det] at h
    exact fun zero => h.ne_zero (by rw [zero, map_zero])
  refine ⟨hd, ?_⟩
  intro w R
  let M := G.map (Int.castRingHom R)
  let P := A.map (Int.castRingHom R)
  have detUnit : IsUnit P.det := (isUnit_iff_isUnit_det P).mp (units w)
  have reconstruct : P * (P⁻¹ * M) = M := by rw [← Matrix.mul_assoc, P.mul_nonsing_inv detUnit, Matrix.one_mul]
  refine ⟨P⁻¹ * M, P.nonsing_inv_mul detUnit, ?_⟩
  intro line member
  apply prefix_fixed_of_rational_span hd G (fun i j => translatedEntry_bound (lines i) j)
    (fun j => translatedEntry line j.val) _ w _ nz reconstruct
  exact translated_label_span hd (Geometry.Dimensions.dimension label live) lines members nz line member

end IntegerMultBounds.MathlibTM2.M6
