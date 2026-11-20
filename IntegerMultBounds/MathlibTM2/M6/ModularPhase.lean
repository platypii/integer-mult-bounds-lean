module

public import IntegerMultBounds.MathlibTM2.M6.ModularScatter
public import IntegerMultBounds.Networks.Certificates.PR589.Framed

/-! Execution of compiled phase instructions using their ordered modular address words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6

open IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589
open Geometry.Moves

variable {R : Type*} [CommRing R]
abbrev AddressStream (R : Type*) := Swap.Shear.State (Fin 8) R → ZMod 2

/-- Each edge consumes one certified label pair and reads through its address word.
Scalar instructions leave the edge trace untouched. -/
def runPhase (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R)) :
    List (FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream R)) →
    List (ℕ × ℕ) → (ℕ → AddressStream R) → (ℕ → AddressStream R)
  | [], _, bank => bank
  | .gate g :: rest, edges, bank => runPhase word rest edges (FramedCircuit.moduleGate g bank)
  | .edge i _ _ :: rest, p :: ps, bank => runPhase word rest ps
      (Function.update bank i fun x => bank i (AffineFieldProgram.run (word p) x))
  | .edge _ _ _ :: _, [], bank => bank

theorem runPhase_eq (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R))
    (frame : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream R))
    (read : ∀ p, CheckedPair p → ∀ f : AddressStream R,
      (fun x => f (AffineFieldProgram.run (word p) x)) = frame p.2 ((frame p.1).symm f))
    (instructions : List (FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream R)))
    (edges : List (ℕ × ℕ))
    (trace : FramedEdgeTrace.pairs instructions = edges.map fun p => (frame p.1, frame p.2))
    (checked : ∀ p ∈ edges, CheckedPair p) (bank : ℕ → AddressStream R) :
    runPhase word instructions edges bank = FramedCircuit.run instructions bank := by
  induction instructions generalizing edges bank with
  | nil => rfl
  | cons instr rest ih =>
    cases instr with
    | gate g => exact ih edges trace checked _
    | edge i old next =>
      cases edges with
      | nil => simp [FramedEdgeTrace.pairs] at trace
      | cons p ps =>
        simp only [FramedEdgeTrace.pairs, List.filterMap_cons, List.map_cons,
          List.cons.injEq, Prod.mk.injEq] at trace
        obtain ⟨⟨rfl, rfl⟩, tail⟩ := trace
        rw [runPhase, read _ (checked p List.mem_cons_self)]
        exact ih ps tail (fun k hk => checked k (List.mem_cons_of_mem _ hk)) _

open Frames (initialRefs finalRefs beforeScatter after234 framedGate scatterFinish)
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- A sequence of identity address reads leaves the entire register bank in place. -/
private theorem runPhase_identity_edges (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R))
    (current desired : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream R))
    (wires : List ℕ) (edges : List (ℕ × ℕ)) (bank : ℕ → AddressStream R)
    (fixed : ∀ p ∈ edges, ∀ s, AffineFieldProgram.run (word p) s = s) :
    runPhase word (FramedCircuit.edges current desired wires) edges bank = bank := by
  induction wires generalizing current edges with
  | nil => rfl
  | cons i rest ih =>
    cases edges with
    | nil => rfl
    | cons p ps =>
      have read : (fun x => bank i (AffineFieldProgram.run (word p) x)) = bank i :=
        funext fun x => congrArg (bank i) (fixed p List.mem_cons_self x)
      simp only [FramedCircuit.edges,runPhase,read,Function.update_eq_self]
      exact ih _ _ (fun q h => fixed q (List.mem_cons_of_mem _ h))

/-- All 661 final alignments may be omitted on the modular stream bank. -/
theorem final_alignment_identity (w : ℕ)
    (frame : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w))))
    (bank : ℕ → AddressStream (ZMod (prime^w))) :
    runPhase (selectedWord w) (FramedCircuit.edges (fun i => frame (Frames.snapshot after234 i))
      (fun i => frame (finalRefs i)) (List.range 661)) Frames.finalEdges bank = bank := by
  apply runPhase_identity_edges
  intro p mem
  have rank := List.mem_map_of_mem (f := fun p : ℕ × ℕ => Geometry.moveRank p.1 p.2) mem
  rw [final_ranks] at rank
  exact (modular_scatter w).choose_spec.2.2.1.zero p (final_checked.1 p mem) (List.mem_replicate.mp rank).2

/-- Run every phase edge through its modular word, including the final alignments.
The nine scatter windows read their temporary through the same word table. -/
def runSelected (frame : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream R))
    (word : ℕ × ℕ → List (AffineFieldProgram.Op (Fin 8) R)) (bank : ℕ → AddressStream R) :=
  let phase := fun (gs : List RawGate) (current : ℕ → ℕ) b => runPhase word
    (FramedCircuit.compile (fun i => frame (current i)) (gs.map (framedGate frame)))
    (Frames.edges gs current) b
  let before := phase (sectionD ++ sectionA) (Frames.snapshot initialRefs) bank
  let after := Copy.lifecycles.foldl (fun b l => scatterWindow word l b) before
  let last := phase (sectionB ++ sectionC) (scatterFinish beforeScatter) after
  runPhase word (FramedCircuit.edges (fun i => frame (Frames.snapshot after234 i))
    (fun i => frame (finalRefs i)) (List.range 661)) Frames.finalEdges last

theorem runSelected_endpoint (w : ℕ) :
    let R := ZMod (prime ^ w)
    let word := selectedWord w
    let frame := selectedFrame w
    LocalMoveProfile word ∧ ∀ stored : Fin 661 → AddressStream R,
      runSelected frame word (FramedCircuit.encode (fun i => frame (Frames.snapshot initialRefs i))
        (Copy.extendStored stored)) =
      FramedCircuit.encode (fun i => frame (Frames.snapshot finalRefs i))
        (FramedCircuit.moduleRun (program.map RawGate.toCircuit) (Copy.extendStored stored)) := by
  intro R word frame
  obtain ⟨read, _, profile, scatter, _⟩ := (modular_scatter w).choose_spec
  refine ⟨profile, ?_⟩
  intro stored
  have checked := phase_checked
  rw [phaseEdges, List.forall_mem_append] at checked
  simp only [runSelected]
  rw [runPhase_eq word frame read _ _ (Frames.final_alignment_pairs _) final_checked.1,
    runPhase_eq word frame read _ _ (Frames.compile_pairs ..) checked.2, scatter,
    runPhase_eq word frame read _ _ (Frames.compile_pairs ..) checked.1]
  exact Framed.execute_endpoint frame stored

end IntegerMultBounds.MathlibTM2.M6
