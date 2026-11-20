module

public import IntegerMultBounds.MathlibTM2.M8.Machine.Segments
public import IntegerMultBounds.Networks.AffineFieldSegments
public import IntegerMultBounds.MathlibTM2.M6.PrefixMove
public import IntegerMultBounds.MathlibTM2.M8.Global.FrameMachine
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Moves.Model

/-! The modular field program for a certified PR589 edge has its billed rank in either direction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl
open M8.Exchange (exchange)

open M8.Height in
private theorem rationalMoveWord_height (d e : ℕ) (C : Matrix (Fin 8) (Fin 8) ℚ)
    (hc : Bounded C (2^6465)) :
    ∀ op ∈ rationalMoveWord d e C, ∀ r ∈ M8.Exchange.opCoeffs op, ht r ≤ coefficientBound := by
  have room : 2^32 ≤ coefficientExponent :=
    le_coefficientExponent (pow_le_pow_right₀ one_le_two (by decide : 32 ≤ 53000))
  have forward := hc.mono (two_pow_le_coefficientBound ((by decide : 6465 ≤ 2^32).trans room))
  have reverse := (adjugate_height C hc).mono (two_pow_le_coefficientBound
    ((by decide : (6465*8+1)*Nat.factorial 8 ≤ 2^32).trans room))
  intro op mem r hr
  simp only [rationalMoveWord, AffineFieldProgram.compile, List.flatMap_append, List.mem_append] at mem
  rcases mem with (left | mid) | right
  · exact M8.Exchange.transformOps_coeffs reverse reverse _ left _ hr
  · obtain ⟨s, hs, inside⟩ := List.mem_flatMap.mp mid
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hs
    simp [AffineFieldProgram.expand] at inside
    subst op
    simp [M8.Exchange.opCoeffs] at hr
  · exact M8.Exchange.transformOps_coeffs forward forward _ right _ hr

/-- One nested MOVE has a single interval exchange between two basis changes. -/
def MoveInterval (i j : Fin 636) (word : List (AffineFieldProgram.Op (Fin 8) ℚ)) : Prop :=
  let d := Geometry.Dimensions.value i.val
  let e := Geometry.Dimensions.value j.val
  ∃ C : Matrix (Fin 8) (Fin 8) ℚ, word = rationalMoveWord (min d e) (max d e) C

/-- The same modular frames serve all certified edges. The field word for each
edge runs in its recorded orientation and uses exactly the rational MOVE rank. -/
private theorem checked_move_words :
    ∃ word : Fin 636 → Fin 636 → List (AffineFieldProgram.Op (Fin 8) ℚ),
    (∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val,j.val) → MoveInterval i j (word i j)) ∧
    (∀ i j op, op ∈ word i j → ∀ r ∈ M8.Exchange.opCoeffs op, M8.Height.ht r ≤ coefficientBound) ∧
    ∀ w : ℕ, let R := ZMod (prime ^ w)
    ∃ P : Fin 636 → Matrix (Fin 8) (Fin 8) R,
      (∀ l, P l * P l = P l) ∧
      (∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val, j.val) → P i * P j = P j * P i) ∧
      (∀ l k, P l k k = if k.val < Geometry.Dimensions.value l.val then 1 else 0) ∧
      ∀ (i j : Fin 636), Geometry.Moves.CheckedPair (i.val, j.val) →
        let q := (word i j).map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime ^ w)))
        (∀ op ∈ q, AffineFieldProgram.Legal op) ∧
        AffineFieldProgram.interchanges q = Geometry.moveRank i.val j.val ∧
        ∀ s, AffineFieldProgram.run q s = exchange (P j) (exchange (P i) s) := by
  classical
  obtain ⟨Q, height, projectors⟩ := compatible_label_projectors
  let dim := fun i : Fin 636 => Geometry.Dimensions.value i.val
  let raw (a b : Fin 636) := rationalMoveWord (dim a) (dim b) (moveBasis (Q b - Q a))
  let incl (a b : Fin 636) := ∀ k ∈ Frames.labels a.val, k ∈ Frames.labels b.val
  have dimLe (a b : Fin 636) (inc : ∀ k ∈ Frames.labels a.val, k ∈ Frames.labels b.val) :
      dim a ≤ dim b := by
    simpa only [dim, Geometry.Dimensions.dimension _ a.isLt, Geometry.Dimensions.dimension _ b.isLt]
      using Submodule.finrank_mono (Geometry.Moves.label_le _ _ inc)
  have comparable (i j : Fin 636) (check : Geometry.Moves.CheckedPair (i.val,j.val)) :
      incl i j ∨ incl j i := by
    rcases check.2.2 with eq | inc | inc
    · change i.val = j.val at eq
      exact Or.inl (fun k h => eq ▸ h)
    · exact Or.inl inc
    · exact Or.inr inc
  refine ⟨fun i j => if incl i j then raw i j else raw j i, ?_, ?_, ?_⟩
  · intro i j check
    change ∃ C, (if incl i j then raw i j else raw j i) = rationalMoveWord (min (dim i) (dim j)) (max (dim i) (dim j)) C
    by_cases h : incl i j
    · exact ⟨_, by simp only [ite_eq_left h, min_eq_left (dimLe i j h), max_eq_right (dimLe i j h)]; rfl⟩
    · have le := dimLe j i ((comparable i j check).resolve_left h)
      exact ⟨_, by simp only [ite_eq_right h, min_eq_right le, max_eq_left le]; rfl⟩
  · intro i j op
    dsimp only
    split <;> exact rationalMoveWord_height _ _ _ (moveBasis_height _ _ (height _) (height _)) op
  intro w R
  obtain ⟨P, reduced, lower, diag, nested⟩ := projectors w
  refine ⟨P, fun l => (nested l l (fun _ h => h)).1, ?_, diag, ?_⟩
  · intro i j h
    rcases h.2.2 with eq | inc | inc
    · obtain rfl : i = j := Fin.ext eq
      rfl
    · exact (nested i j inc).2.trans (nested i j inc).1.symm
    · exact (nested j i inc).1.trans (nested j i inc).2.symm
  have bounded : ∀ i : Fin 636, dim i ≤ 8 := by decide +kernel
  have oriented (a b : Fin 636) (inc : ∀ k ∈ Frames.labels a.val, k ∈ Frames.labels b.val) :
      let q := (raw a b).map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime ^ w)))
      (∀ op ∈ q, AffineFieldProgram.Legal op) ∧
      AffineFieldProgram.interchanges q = dim b - dim a ∧
      ∀ s, AffineFieldProgram.run q s = exchange (P a) (exchange (P b) s) := by
    let m := prime ^ w
    let C := Swap.Modular.reduce m (moveBasis (Q b - Q a))
    have adm (l) : Swap.Modular.Admissible m (Q l) := fun i j => (reduced l i j).1
    have frame (l) : Swap.Modular.reduce m (Q l) = P l := Matrix.ext fun i j => (reduced l i j).2.symm
    have basis : C = moveBasis (P b - P a) := by
      rw [show C = _ from (moveBasis_reduce m _ (ModularFrameSchedule.admissible_sub m (adm b) (adm a))).2,
        ModularFrameSchedule.reduce_sub m (adm b) (adm a), frame, frame]
    obtain ⟨tri, _, ones, inv, run⟩ := nested_label_moves w P lower diag nested a b inc
    rw [← basis] at tri ones inv run
    have unit : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).mpr (Matrix.isUnit_det_of_right_inverse inv)
    obtain ⟨legal, count, correct⟩ := compile_prefixMove _ _ (bounded a) (bounded b) C tri unit
    have det : C.det = 1 := by simp [C.det_of_isLowerTriangular tri, ones]
    dsimp only [raw]
    rw [rationalMoveWord_reduce m _ _ _ (moveBasis_reduce m _
      (ModularFrameSchedule.admissible_sub m (adm b) (adm a))).1 det]
    exact ⟨legal, count, fun s => (correct s).trans (run s)⟩
  intro i j check
  rw [Geometry.Moves.rank _ check]

  by_cases inc : incl i j
  · simp only [ite_eq_left inc]
    obtain ⟨legal, count, run⟩ := oriented i j inc
    obtain ⟨ji, ij⟩ := nested i j inc
    refine ⟨legal, by change _ = (dim j - dim i) + (dim i - dim j); rw [count, Nat.sub_eq_zero_of_le (dimLe i j inc), Nat.add_zero], ?_⟩
    intro s
    rw [run, M8.Global.exchange_exchange, M8.Global.exchange_exchange, ij, ji, add_comm (P i)]
  · simp only [ite_eq_right inc]
    have inc := (comparable i j check).resolve_left inc
    obtain ⟨legal, count, run⟩ := oriented j i inc
    exact ⟨legal, by change _ = (dim j - dim i) + (dim i - dim j); rw [count, Nat.sub_eq_zero_of_le (dimLe j i inc), Nat.zero_add], run⟩

private theorem legal_of_prime (op : AffineFieldProgram.Op (Fin 8) ℚ)
    (h : AffineFieldProgram.Legal (AffineFieldProgram.mapOp (Swap.Modular.ratMod prime) op)) :
    AffineFieldProgram.Legal op := by
  let : Fact prime.Prime := ⟨prime_prime⟩
  have scale (r : ℚ) (hr : IsUnit (Swap.Modular.ratMod prime r)) : IsUnit r := by
    apply isUnit_iff_ne_zero.mpr
    intro zero
    exact hr.ne_zero (zero ▸ Swap.Modular.ratMod_zero prime)
  cases op with
  | affineH op | affineD op =>
    cases op with
    | scale i r => exact scale r h
    | shift i j r => exact h
  | _ => trivial

/-- All nonrecursive segments of the same checked word have fixed clean
coordinate machines at every width, via `Segments.realizes`. -/
theorem checked_move_programs :
    ∃ word : Fin 636 → Fin 636 → List (AffineFieldProgram.Op (Fin 8) ℚ),
    (∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val,j.val) → MoveInterval i j (word i j)) ∧
    (∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val,j.val) →
      ∀ ops, (∀ op ∈ ops, op ∈ word i j) → (∀ op ∈ ops, AffineFieldCoordinates.Nonrecursive op) →
        M8.Machine.Segments.Good ops) ∧
    ∀ w : ℕ, let R := ZMod (prime ^ w)
    ∃ P : Fin 636 → Matrix (Fin 8) (Fin 8) R,
      (∀ l, P l * P l = P l) ∧
      (∀ i j : Fin 636, Geometry.Moves.CheckedPair (i.val, j.val) → P i * P j = P j * P i) ∧
      (∀ l k, P l k k = if k.val < Geometry.Dimensions.value l.val then 1 else 0) ∧
      ∀ (i j : Fin 636), Geometry.Moves.CheckedPair (i.val, j.val) →
        let q := (word i j).map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime ^ w)))
        (∀ op ∈ q, AffineFieldProgram.Legal op) ∧
        AffineFieldProgram.interchanges q = Geometry.moveRank i.val j.val ∧
        ∀ s, AffineFieldProgram.run q s = exchange (P j) (exchange (P i) s) := by
  obtain ⟨word, interval, height, widths⟩ := checked_move_words
  refine ⟨word, interval, ?_, widths⟩
  intro i j checked ops subset atoms
  obtain ⟨P, _, _, _, edge⟩ := widths 1
  obtain ⟨legal, _, _⟩ := edge i j checked
  have rational (op) (hop : op ∈ ops) : AffineFieldProgram.Legal op := by
    apply legal_of_prime
    have h := legal _ (List.mem_map_of_mem (f := AffineFieldProgram.mapOp _) (subset op hop))
    rw [pow_one] at h
    exact h
  refine ⟨rational, ?_, atoms⟩
  intro op hop
  apply M8.Machine.Coordinates.CoeffBounded.supported _ (rational op hop)
  intro r hr
  have h := height i j op (subset op hop) r hr
  exact ⟨(M8.Height.num_le_ht r).trans h, (M8.Height.den_le_ht r).trans h⟩

end IntegerMultBounds.MathlibTM2.M6
