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

open IntegerMultBounds.Swap.Shear (Op State run interchanges)

/-- Swap matching coordinates in the two address halves. -/
def coordinateSwaps {ι R : Type*} (ks : List ι) : List (Op ι R) :=
  ks.map fun k => .interchange k k

theorem coordinateSwaps_run {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (ks : List ι) (distinct : ks.Nodup) (s : State ι R) :
    run (coordinateSwaps ks) s = exchange (M8.Exchange.indicator ks) s := by
  have eval (l : List ι) (t : State ι R) :
      exchange (M8.Exchange.indicator l) t =
        (fun k => if k ∈ l then t.2 k else t.1 k,
         fun k => if k ∈ l then t.1 k else t.2 k) := by
    apply Prod.ext <;> funext k <;>
      simp only [exchange, sub_mulVec, one_mulVec, Pi.add_apply, Pi.sub_apply,
        M8.Exchange.mulVec_indicator] <;> split_ifs <;> simp
  rw [eval]
  induction ks generalizing s with
  | nil => simp [coordinateSwaps]
  | cons k ks ih =>
    obtain ⟨fresh, tail⟩ := List.nodup_cons.mp distinct
    change run (coordinateSwaps ks) ((Op.interchange k k).run s) = _
    rw [ih tail]
    apply Prod.ext <;> funext j <;> by_cases eq : j = k
    all_goals simp_all [Op.run, Function.update]

/-- The instruction word for the middle of a MOVE on eight address coordinates. -/
def intervalSwaps {R : Type*} (d e : ℕ) : List (Op (Fin 8) R) :=
  coordinateSwaps ((List.finRange 8).filter fun k => d ≤ k.val ∧ k.val < e)

theorem intervalSwaps_run {R : Type*} [CommRing R] (d e : ℕ) (s : State (Fin 8) R) :
    run (intervalSwaps d e) s =
      exchange (diagonal fun k => if d ≤ k.val ∧ k.val < e then 1 else 0) s := by
  rw [intervalSwaps, coordinateSwaps_run _ ((List.nodup_finRange 8).filter _)]
  simp [M8.Exchange.indicator]

theorem intervalSwaps_interchanges {R : Type*} (d e : ℕ) (hd : d ≤ 8) (he : e ≤ 8) :
    interchanges (intervalSwaps (R := R) d e) = e - d := by
  have count : ∀ a b : Fin 9, ((List.finRange 8).filter fun k =>
      a.val ≤ k.val ∧ k.val < b.val).length = b.val - a.val := by decide +kernel
  simpa [intervalSwaps, coordinateSwaps, interchanges, Op.isInterchange, List.filter_map]
    using count ⟨d, by omega⟩ ⟨e, by omega⟩

/-- Conjugate the interval swaps by a change of basis on each address half. -/
noncomputable def prefixMoveProgram {R : Type*} [CommRing R] (d e : ℕ)
    (C : Matrix (Fin 8) (Fin 8) R) : List (Op (Fin 8) R) :=
  [.transformH C⁻¹, .transformD C⁻¹] ++ intervalSwaps d e ++ [.transformH C, .transformD C]

theorem prefixMoveProgram_interchanges {R : Type*} [CommRing R] (d e : ℕ)
    (hd : d ≤ 8) (he : e ≤ 8) (C : Matrix (Fin 8) (Fin 8) R) :
    interchanges (prefixMoveProgram d e C) = e - d := by
  simpa [prefixMoveProgram, interchanges, Op.isInterchange] using
    intervalSwaps_interchanges (R := R) d e hd he

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
        ∃ C : Matrix (Fin 8) (Fin 8) R, C.IsLowerTriangular ∧ C⁻¹.IsLowerTriangular ∧
          (∀ k, C k k = 1) ∧ C * C⁻¹ = 1 ∧ ∀ s,
          run (prefixMoveProgram (dim i) (dim j) C) s = exchange (P i) (exchange (P j) s) := by
  intro R dim P lower diag nested i j incl
  let E : Matrix (Fin 8) (Fin 8) R := diagonal fun k => if dim i ≤ k.val ∧ k.val < dim j then 1 else 0
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
  simp only [prefixMoveProgram, IntegerMultBounds.Swap.Shear.run_append, intervalSwaps_run]
  change transform C C (exchange E (transform C⁻¹ C⁻¹ s)) = _
  rw [Cover.Weighted.exchange_conj _ _ _ (C.mul_nonsing_inv unit), basis, Matrix.mul_assoc,
    C.mul_nonsing_inv unit, Matrix.mul_one, M8.Exchange.exchange_comp _ _ ij]

end IntegerMultBounds.MathlibTM2.M6
