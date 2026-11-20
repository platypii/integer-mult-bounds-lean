module

public import IntegerMultBounds.MathlibTM2.M6.CheckedMove
public import IntegerMultBounds.Networks.Certificates.PR589.Geometry.Moves.Profile

/-! Ordered modular programs for the phase and final-alignment MOVEs of PR589. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open Matrix IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589
open Geometry.Moves
open IntegerMultBounds.Networks.Shared50ModularControl
open M8.Exchange (exchange)

/-- Address changes on the retained sources when forming the scatter temporaries. -/
def retainedCopyEdges : List (ℕ × ℕ) :=
  (Frames.retained.map Frames.beforeScatter).map fun label => (label, 0)

theorem retainedCopy_checked : (∀ p ∈ retainedCopyEdges, CheckedPair p) ∧
    retainedCopyEdges.map value = List.replicate 9 7 := by
  rw [retainedCopyEdges, Frames.retained_frames]
  decide +kernel

/-- Local interchange charges of the very words used to change stream addresses. -/
structure LocalMoveProfile {R : Type*} [CommRing R] (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R)) : Prop where
  legal : ∀ p, CheckedPair p → ∀ op ∈ word p, AffineFieldProgram.Legal op
  phases : (phaseEdges.map word).map AffineFieldProgram.interchanges = phaseValues
  alignment : (Frames.finalEdges.map word).map AffineFieldProgram.interchanges = List.replicate 661 0
  copies : (retainedCopyEdges.map word).map AffineFieldProgram.interchanges = List.replicate 9 7
  histogram :
    let phase := (phaseEdges.map word).map AffineFieldProgram.interchanges
    let copy := (retainedCopyEdges.map word).map AffineFieldProgram.interchanges
    (List.range 9).map (((phase.filter (· ≠ 0)) ++ copy).count) = [0, 1323, 1342, 79, 44, 102, 11, 19, 0]

/-- Choose the modular program once per certified pair. Looking up the programs in
execution order reproduces the full phase profile and the zero final-alignment bill. -/
theorem modular_move_profile :
    ∃ raw : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) ℚ),
      (∀ p ∈ retainedCopyEdges, ∃ C, raw p = rationalMoveWord 0 7 C) ∧
      (∀ p, CheckedPair p → ∀ ops ∈ AffineFieldSegments.runs (AffineFieldSegments.split (raw p)),
        M8.Machine.Segments.Good ops) ∧
    ∀ w : ℕ, let R := ZMod (prime ^ w)
    let word := fun p => (raw p).map (AffineFieldProgram.mapOp (Swap.Modular.ratMod (prime ^ w)))
    ∃ P : Fin 636 → Matrix (Fin 8) (Fin 8) R,
      (∀ l, P l * P l = P l) ∧
      (∀ i j : Fin 636, CheckedPair (i.val, j.val) → P i * P j = P j * P i) ∧
      (∀ p (h : CheckedPair p), ∀ s, AffineFieldProgram.run (word p) s =
          exchange (P ⟨p.2, h.2.1⟩) (exchange (P ⟨p.1, h.1⟩) s)) ∧
      LocalMoveProfile word := by
  classical
  obtain ⟨raw, interval, segments, widths⟩ := checked_move_programs
  let lookup (p : ℕ × ℕ) := if h : CheckedPair p then raw ⟨p.1,h.1⟩ ⟨p.2,h.2.1⟩ else []
  refine ⟨lookup, ?_, ?_, ?_⟩
  · have dims : ∀ p ∈ retainedCopyEdges,
        Geometry.Dimensions.value p.1 = 7 ∧ Geometry.Dimensions.value p.2 = 0 := by
      rw [retainedCopyEdges, Frames.retained_frames]
      decide +kernel
    intro p member
    have checked := retainedCopy_checked.1 p member
    obtain ⟨C, eq⟩ := interval ⟨p.1,checked.1⟩ ⟨p.2,checked.2.1⟩ checked
    refine ⟨C, ?_⟩
    simpa only [lookup, dite_eq_left checked, (dims p member).1, (dims p member).2,
      Nat.min_zero, Nat.max_zero] using eq
  · intro p h
    simpa only [lookup, dite_eq_left h] using segments ⟨p.1,h.1⟩ ⟨p.2,h.2.1⟩ h
  intro w R word
  obtain ⟨P, idem, commute, _, programs⟩ := widths w
  have spec (p : ℕ × ℕ) (h : CheckedPair p) :
      (∀ op ∈ word p, AffineFieldProgram.Legal op) ∧
      AffineFieldProgram.interchanges (word p) = Geometry.moveRank p.1 p.2 ∧
      ∀ s, AffineFieldProgram.run (word p) s =
        exchange (P ⟨p.2, h.2.1⟩) (exchange (P ⟨p.1, h.1⟩) s) := by
    simpa only [word, lookup, dite_eq_left h] using programs ⟨p.1,h.1⟩ ⟨p.2,h.2.1⟩ h
  have counts (edges : List (ℕ × ℕ)) (checked : ∀ p ∈ edges, CheckedPair p) :
      (edges.map word).map AffineFieldProgram.interchanges =
        edges.map (fun p => Geometry.moveRank p.1 p.2) := by
    rw [List.map_map]
    exact List.map_congr_left fun p hp => (spec p (checked p hp)).2.1
  have phase := (counts _ phase_checked).trans phase_ranks
  have copies := (counts _ retainedCopy_checked.1).trans
    ((profile _ retainedCopy_checked.1).trans retainedCopy_checked.2)
  refine ⟨P, idem, commute, fun p h => (spec p h).2.2, fun p h => (spec p h).1, phase,
    (counts _ final_checked.1).trans final_ranks, copies, ?_⟩
  rw [phase, copies, ← phase_ranks, ← copyRanks_eq]
  exact localPaid_histogram

end IntegerMultBounds.MathlibTM2.M6
