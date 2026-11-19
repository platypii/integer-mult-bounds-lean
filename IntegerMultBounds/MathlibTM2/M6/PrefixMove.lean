module

public import IntegerMultBounds.MathlibTM2.M6.PrefixLabel
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.PortFrame
public import IntegerMultBounds.MathlibTM2.Cover.Weighted

/-! A nested PR589 MOVE exchanges a single interval in triangular coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl
open M8.Exchange (exchange transform)

/-- One family of tape-ring frames serves every nested pair. In coordinates given by
a unitriangular adapter, its MOVE exchanges precisely the newly gained prefix positions. -/
theorem nested_label_moves (w : ℕ) :
    let R := ZMod (prime ^ w)
    let dim := fun i : Fin 636 => Geometry.Dimensions.value i.val
    ∀ P : Fin 636 → Matrix (Fin 8) (Fin 8) R,
      (∀ l i j, i < j → P l i j = 0) →
      (∀ l i, P l i i = if i.val < dim l then 1 else 0) →
      (∀ i j : Fin 636, (∀ k ∈ Frames.labels i.val, k ∈ Frames.labels j.val) →
        P j * P i = P i ∧ P i * P j = P i) →
      ∀ i j : Fin 636, (∀ k ∈ Frames.labels i.val, k ∈ Frames.labels j.val) →
        let E : Matrix (Fin 8) (Fin 8) R :=
          diagonal fun k => if dim i ≤ k.val ∧ k.val < dim j then 1 else 0
        ∃ C : Matrix (Fin 8) (Fin 8) R, C.IsLowerTriangular ∧ C⁻¹.IsLowerTriangular ∧
          (∀ k, C k k = 1) ∧ C * C⁻¹ = 1 ∧ ∀ s,
          transform C C (exchange E (transform C⁻¹ C⁻¹ s)) = exchange (P i) (exchange (P j) s) := by
  intro R dim P lower diag nested i j incl E
  have sub : Geometry.label i.val ≤ Geometry.label j.val := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, rfl⟩
    exact Geometry.root_mem _ _ (incl k hk)
  have le := Submodule.finrank_mono sub
  rw [Geometry.Dimensions.dimension _ i.isLt, Geometry.Dimensions.dimension _ j.isLt] at le
  change dim i ≤ dim j at le
  let U := P j - P i
  have entry (k : Fin 8) : U k k = if dim i ≤ k.val ∧ k.val < dim j then 1 else 0 := by
    simp only [U, Matrix.sub_apply, diag]
    split_ifs <;> first | omega | simp
  obtain ⟨ji, ij⟩ := nested i j incl
  have idem (l) := (nested l l (fun _ h => h)).1
  have tri : U.IsLowerTriangular := fun {a b} h => by
    have lt : a < b := h
    simp [U, Matrix.sub_apply, lower j a b lt, lower i a b lt]
  obtain ⟨C, hC, ones, unit, basis⟩ := Nine.triangular_projector_basis U tri
    (M8.Exchange.sub_idempotent _ _ (idem i) (idem j) ij ji)
    (fun k => by rw [entry]; split <;> simp)
  have eq : diagonal (fun k => U k k) = E := congrArg diagonal (funext entry)
  rw [eq] at basis
  let := C.invertibleOfIsUnitDet unit
  refine ⟨C, hC, blockTriangular_inv_of_blockTriangular hC, ones, C.mul_nonsing_inv unit, ?_⟩
  intro s
  rw [Cover.Weighted.exchange_conj _ _ _ (C.mul_nonsing_inv unit), basis, Matrix.mul_assoc,
    C.mul_nonsing_inv unit, Matrix.mul_one, M8.Exchange.exchange_comp _ _ ij]

end IntegerMultBounds.MathlibTM2.M6
