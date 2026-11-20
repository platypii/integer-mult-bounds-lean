module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyLabel
public import IntegerMultBounds.MathlibTM2.M6.ModularPhase

/-! Compose the PR589 frame changes and scalar instructions on the permanent
owner tapes, and read their result in the modular phase semantics. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open IntegerMultBounds.Networks.Certificates.PR589
open Shared50ModularControl (prime)

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

noncomputable def phaseRead {k w W : ℕ} (owner : Fin 661 ↪ Fin k)
    (data : Fin k → Fin ((prime^w)^16*W) → ZMod 2) (j : Fin W) : ℕ → AddressStream (ZMod (prime^w)) :=
  Copy.extendStored fun r s => data (owner r) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j)

private theorem phaseRead_gate {k w W : ℕ} (owner : Fin 661 ↪ Fin k) (g : RawGate)
    (scheduled : g ∈ program) (data out : Fin k → Fin ((prime^w)^16*W) → ZMod 2)
    (action : ∀ r : Fin 661, ∀ i, out (owner r) i =
      g.toCircuit.run (Copy.extendStored (fun r => data (owner r) i)) r.val) (j : Fin W) :
    phaseRead owner out j = FramedCircuit.moduleGate g.toCircuit (phaseRead owner data j) := by
  funext r s
  rw [FramedCircuit.moduleGate_pointwise]
  have inputs : (fun i => phaseRead owner data j i s) =
      Copy.extendStored (fun i => data (owner i) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j)) := by
    funext i
    by_cases h : i < 661 <;> simp [phaseRead,Copy.extendStored,h]
  rw [inputs]
  by_cases h : r < 661
  · simpa [phaseRead,Copy.extendStored,h] using action ⟨r,h⟩ (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j)
  · have ne : r ≠ g.target := fun eq => h (eq ▸ (register_bounds g scheduled).1)
    rw [RawGate.run_eq,Function.update_of_ne ne]
    simp [phaseRead,Copy.extendStored,h]

private theorem phaseRead_edge {k w W : ℕ} (owner : Fin 661 ↪ Fin k) (r : Fin 661) (p : ℕ × ℕ)
    (data out : Fin k → Fin ((prime^w)^16*W) → ZMod 2)
    (other : ∀ i, i ≠ owner r → out i = data i)
    (read : ∀ s j, out (owner r) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) =
      data (owner r) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed
        (AffineFieldProgram.run (selectedWord w p) s)) j)) (j : Fin W) :
    phaseRead owner out j = Function.update (phaseRead owner data j) r.val
      (fun s => phaseRead owner data j r.val (AffineFieldProgram.run (selectedWord w p) s)) := by
  funext i s
  by_cases eq : i = r.val
  · subst i
    simpa [phaseRead,Copy.extendStored,r.isLt] using read s j
  · rw [Function.update_of_ne eq]
    by_cases hi : i < 661
    · have apart : owner ⟨i,hi⟩ ≠ owner r := fun h => eq (congrArg Fin.val (owner.injective h))
      simp [phaseRead,Copy.extendStored,hi,other _ apart]
    · simp [phaseRead,Copy.extendStored,hi]

open M8.Machine in
noncomputable def edgeBasis [Net] {k : ℕ} (owner : Fin 661 ↪ Fin k) (p : ℕ × ℕ) : ℕ := by
  classical
  exact if h : Geometry.Moves.CheckedPair p then
    ∑ r : Fin 661, (phaseEdge_stage (owner r) h).choose else 0

open M8.Machine in
noncomputable def phaseEdgeBudget [Net] {k : ℕ} (owner : Fin 661 ↪ Fin k) (w W : ℕ) (p : ℕ × ℕ) :=
  let a := Geometry.Dimensions.value p.1
  let b := Geometry.Dimensions.value p.2
  let child := phaseIntervalChild (min a b) (max a b) w W
  let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
  if Geometry.moveRank p.1 p.2 = 0 then 0 else
    phaseWork (edgeBasis owner p) ((prime^w)^16*W) (ArbitraryWidthOriginalRun.cost child hs)

def scalarWork {w : ℕ} (V : ℕ) : FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^w))) → ℕ
  | .gate g => 76*g.terms.length*V
  | .edge .. => 0

open M8.Machine in
/-- Execute an ordered list of framed instructions. Each tape stage contributes
one join, and only the encountered positive-rank edges need recursive work. -/
theorem phaseInstructions_stage [Net] {k w W : ℕ} (owner : Fin 661 ↪ Fin k)
    (hw : 0 < w) (hW : 0 < W)
    (instructions : List (FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^w)))))
    (edges : List (ℕ × ℕ)) (checked : ∀ p ∈ edges, Geometry.Moves.CheckedPair p)
    (valid : ∀ instr ∈ instructions, match instr with
      | .edge i _ _ => i < 661
      | .gate gate => ∃ g ∈ program, gate = g.toCircuit) :
    let V := (prime^w)^16*W
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      stage.cost ≤ (instructions.map (scalarWork V)).sum +
        (edges.map (phaseEdgeBudget owner w W)).sum + instructions.length ∧
      (∀ data j, phaseRead owner (stage.transform data) j =
        runPhase (selectedWord w) instructions edges (phaseRead owner data j)) ∧
      ∀ data i, (∀ r, owner r ≠ i) → stage.transform data i = data i := by
  classical
  intro V
  have hk : 0 < k := Nat.zero_lt_of_lt (owner 0).isLt
  have pos : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  induction instructions generalizing edges with
  | nil => exact ⟨SharedBankStage.identity _ hk,by simp [SharedBankStage.identity],fun _ _ => rfl,fun _ _ _ => rfl⟩
  | cons instr rest ih =>
    have head := valid instr List.mem_cons_self
    have tail := fun x (mem : x ∈ rest) => valid x (List.mem_cons_of_mem _ mem)
    cases instr with
    | gate g =>
      obtain ⟨raw,scheduled,rfl⟩ := head
      obtain ⟨step,price,acts⟩ := phaseRawGate_stage owner raw scheduled pos
      obtain ⟨next,budget,reads,off⟩ := ih edges checked tail
      refine ⟨SharedBankStage.compose step next,?_,?_,?_⟩
      · change step.cost+next.cost+1 ≤ _
        simp only [List.map_cons,List.sum_cons,List.length_cons,scalarWork,RawGate.toCircuit,List.length_map]
        omega
      · intro data j
        rw [show (SharedBankStage.compose step next).transform data = next.transform (step.transform data) from rfl,reads,
          phaseRead_gate owner raw scheduled data _ (acts data).2 j]
        rfl
      · intro data i outside
        exact (off _ i outside).trans ((acts data).1 i (outside _).symm)
    | edge i old newFrame =>
      cases edges with
      | nil => exact ⟨SharedBankStage.identity _ hk,Nat.zero_le _,fun _ _ => rfl,fun _ _ _ => rfl⟩
      | cons p ps =>
        let r : Fin 661 := ⟨i,head⟩
        have check := checked p List.mem_cons_self
        let cert := phaseEdge_stage (owner r) check
        obtain ⟨step,price,acts⟩ := cert.choose_spec w W hw hW
        obtain ⟨next,budget,reads,off⟩ := ih ps (fun q mem => checked q (List.mem_cons_of_mem _ mem)) tail
        have rate : cert.choose ≤ edgeBasis owner p := by
          simp only [edgeBasis,dite_eq_left check]
          exact Finset.single_le_sum (f := fun j : Fin 661 => (phaseEdge_stage (owner j) check).choose)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)
        have charge : step.cost ≤ phaseEdgeBudget owner w W p := by
          rw [price]
          unfold phaseEdgeBudget
          split <;> simp only [phaseWork]
          · rfl
          · exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ rate) _) _) _
        refine ⟨SharedBankStage.compose step next,?_,?_,?_⟩
        · change step.cost+next.cost+1 ≤ _
          simp only [List.map_cons,List.sum_cons,List.length_cons,scalarWork]
          omega
        · intro data j
          rw [show (SharedBankStage.compose step next).transform data = next.transform (step.transform data) from rfl,reads,
            phaseRead_edge owner r p data _ (acts data).1 (acts data).2 j]
          rfl
        · intro data i outside
          exact (off _ i outside).trans ((acts data).1 i (outside _).symm)

private def validInstruction {w : ℕ} : FramedCircuit.Instruction ℕ (ZMod 2) (AddressStream (ZMod (prime^w))) → Prop
  | .edge i _ _ => i < 661
  | .gate gate => ∃ g ∈ program, gate = g.toCircuit

private theorem compiled_valid {w : ℕ}
    (frame : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w))))
    (current : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w))))
    (gs : List RawGate) (scheduled : ∀ g ∈ gs, g ∈ program) :
    ∀ instr ∈ FramedCircuit.compile current (gs.map (Frames.framedGate frame)), validInstruction instr := by
  have aligned (wires : List ℕ) (bounds : ∀ i ∈ wires, i < 661) (a b : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w)))) :
      ∀ instr ∈ FramedCircuit.edges a b wires, validInstruction instr := by
    induction wires generalizing a with
    | nil => simp [FramedCircuit.edges]
    | cons i rest ih =>
      intro instr mem
      rcases List.mem_cons.mp mem with rfl | h
      · exact bounds i List.mem_cons_self
      · exact ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) _ instr h
  induction gs generalizing current with
  | nil => simp [FramedCircuit.compile]
  | cons g gs ih =>
    intro instr mem
    have raw := scheduled g List.mem_cons_self
    rcases List.mem_append.mp mem with head | tail
    · rcases List.mem_append.mp head with edge | gate
      · apply aligned _ _ _ _ instr edge
        rw [show (Frames.framedGate frame g).gate = g.toCircuit from rfl,Frames.touched_toCircuit]
        exact Frames.bounded_touched program program_bounded g raw
      · obtain rfl := List.mem_singleton.mp gate
        exact ⟨g,raw,rfl⟩
    · exact ih _ (fun q h => scheduled q (List.mem_cons_of_mem _ h)) instr tail

open M8.Machine in
/-- Both literal phase lists on opposite sides of the COPY windows run on the
same owner representation, from their respective certified frame snapshots. -/
theorem invocationPhase_stage [Net] {k w W : ℕ} (owner : Fin 661 ↪ Fin k) (hw : 0 < w) (hW : 0 < W)
    (afterScatter : Bool) :
    let gates := if afterScatter then sectionB ++ sectionC else sectionD ++ sectionA
    let current := if afterScatter then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let frame := selectedFrame w
    let instructions := FramedCircuit.compile (fun i => frame (current i)) (gates.map (Frames.framedGate frame))
    let edges := Frames.edges gates current
    let V := (prime^w)^16*W
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      stage.cost ≤ (instructions.map (scalarWork V)).sum + (edges.map (phaseEdgeBudget owner w W)).sum + instructions.length ∧
      (∀ data j, phaseRead owner (stage.transform data) j =
        runPhase (selectedWord w) instructions edges (phaseRead owner data j)) ∧
      ∀ data i, (∀ r, owner r ≠ i) → stage.transform data i = data i := by
  intro gates current frame instructions edges V
  have check := Geometry.Moves.phase_checked
  rw [Geometry.Moves.phaseEdges,List.forall_mem_append] at check
  have good : ∀ p ∈ edges, Geometry.Moves.CheckedPair p := by
    cases afterScatter
    · exact check.1
    · exact check.2
  apply phaseInstructions_stage owner hw hW instructions edges good
  apply compiled_valid
  intro g mem
  cases afterScatter <;> simp only [gates,Bool.false_eq_true,ite_false,ite_true,List.mem_append] at mem
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append.mpr mem)))
  · rcases mem with b | c
    · exact List.mem_append_left _ (List.mem_append_right _ b)
    · exact List.mem_append_right _ c

end IntegerMultBounds.MathlibTM2.M6.BitNode
