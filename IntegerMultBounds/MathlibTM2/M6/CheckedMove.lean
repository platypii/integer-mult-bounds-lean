module

public import IntegerMultBounds.MathlibTM2.M6.PrefixMove
public import IntegerMultBounds.MathlibTM2.M8.Global.FrameMachine
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Moves.Model

/-! The modular field program for a certified PR589 edge has its billed rank in either direction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589
open IntegerMultBounds.Networks.Shared50ModularControl
open M8.Exchange (exchange)

/-- The same modular frames serve all certified edges. The field word for each
edge runs in its recorded orientation and uses exactly the rational MOVE rank. -/
theorem checked_move_programs (w : ℕ) :
    let R := ZMod (prime ^ w)
    ∃ P : Fin 636 → Matrix (Fin 8) (Fin 8) R,
      (∀ l, P l * P l = P l) ∧
      (∀ l k, P l k k = if k.val < Geometry.Dimensions.value l.val then 1 else 0) ∧
      ∀ (i j : Fin 636), Geometry.Moves.CheckedPair (i.val, j.val) →
        ∃ q : List (AffineFieldProgram.Op (Fin 8) R),
          (∀ op ∈ q, AffineFieldProgram.Legal op) ∧
          AffineFieldProgram.interchanges q = Geometry.moveRank i.val j.val ∧
          ∀ s, AffineFieldProgram.run q s = exchange (P j) (exchange (P i) s) := by
  intro R
  obtain ⟨P, lower, diag, nested⟩ := compatible_label_projectors w
  refine ⟨P, fun l => (nested l l (fun _ h => h)).1, diag, ?_⟩
  let dim := fun i : Fin 636 => Geometry.Dimensions.value i.val
  have bounded : ∀ i : Fin 636, dim i ≤ 8 := by decide +kernel
  have oriented (a b : Fin 636) (inc : ∀ k ∈ Frames.labels a.val, k ∈ Frames.labels b.val) :
      ∃ q : List (AffineFieldProgram.Op (Fin 8) R),
        (∀ op ∈ q, AffineFieldProgram.Legal op) ∧
        AffineFieldProgram.interchanges q = dim b - dim a ∧
        ∀ s, AffineFieldProgram.run q s = exchange (P a) (exchange (P b) s) := by
    obtain ⟨C, tri, _, _, inv, run⟩ := nested_label_moves w P lower diag nested a b inc
    have unit := (Matrix.isUnit_iff_isUnit_det C).mpr (Matrix.isUnit_det_of_right_inverse inv)
    obtain ⟨legal, count, correct⟩ := compile_prefixMove _ _ (bounded a) (bounded b) C tri unit
    exact ⟨_, legal, count, fun s => (correct s).trans (run s)⟩
  have dimLe (a b : Fin 636) (inc : ∀ k ∈ Frames.labels a.val, k ∈ Frames.labels b.val) :
      dim a ≤ dim b := by
    simpa only [dim, Geometry.Dimensions.dimension _ a.isLt, Geometry.Dimensions.dimension _ b.isLt]
      using Submodule.finrank_mono (Geometry.Moves.label_le _ _ inc)
  intro i j check
  rw [Geometry.Moves.rank _ check]
  change ∃ q, _ ∧ AffineFieldProgram.interchanges q = (dim j - dim i) + (dim i - dim j) ∧ _
  have cases : (∀ k ∈ Frames.labels i.val, k ∈ Frames.labels j.val) ∨
      (∀ k ∈ Frames.labels j.val, k ∈ Frames.labels i.val) := by
    rcases check.2.2 with eq | inc | inc
    · change i.val = j.val at eq
      exact Or.inl (fun k h => eq ▸ h)
    · exact Or.inl inc
    · exact Or.inr inc
  rcases cases with inc | inc
  · obtain ⟨q, legal, count, run⟩ := oriented i j inc
    obtain ⟨ji, ij⟩ := nested i j inc
    refine ⟨q, legal, by rw [count, Nat.sub_eq_zero_of_le (dimLe i j inc), Nat.add_zero], ?_⟩
    intro s
    rw [run, M8.Global.exchange_exchange, M8.Global.exchange_exchange, ij, ji, add_comm (P i)]
  · obtain ⟨q, legal, count, run⟩ := oriented j i inc
    exact ⟨q, legal, by rw [count, Nat.sub_eq_zero_of_le (dimLe j i inc), Nat.zero_add], run⟩

end IntegerMultBounds.MathlibTM2.M6
