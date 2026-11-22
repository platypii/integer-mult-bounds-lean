module

public import IntegerMultBounds.Machine.RowPaddingConstructedAlphabet
public import IntegerMultBounds.Machine.LabelRowXor
public import IntegerMultBounds.MathlibTM2.M6.BitCopyLabel
public import IntegerMultBounds.MathlibTM2.M6.BitNodeCost
public import IntegerMultBounds.MathlibTM2.M6.BitPortRun

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

theorem phaseRead_gate {k w W : ℕ} (owner : Fin 661 ↪ Fin k) (g : RawGate)
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

theorem phaseRead_edge {k w W : ℕ} (owner : Fin 661 ↪ Fin k) (r : Fin 661) (p : ℕ × ℕ)
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
noncomputable def phaseChildCost [Net] (w W : ℕ) (p : ℕ × ℕ) :=
  let a := Geometry.Dimensions.value p.1
  let b := Geometry.Dimensions.value p.2
  let child := phaseIntervalChild (min a b) (max a b) w W
  let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
  ArbitraryWidthOriginalRun.cost child hs

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
      obtain ⟨step,_,_,price,acts⟩ := phaseRawGate_stage owner raw scheduled pos
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

/-- The selected phases use only scheduled scalar gates, valid owner indices,
and checked frame changes on both sides of the scatter. -/
theorem invocationPhase_valid (w : ℕ) (afterScatter : Bool) :
    let gates := if afterScatter then sectionB ++ sectionC else sectionD ++ sectionA
    let current := if afterScatter then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let frame := selectedFrame w
    let instructions := FramedCircuit.compile (fun i => frame (current i)) (gates.map (Frames.framedGate frame))
    let edges := Frames.edges gates current
    (∀ p ∈ edges, Geometry.Moves.CheckedPair p) ∧ ∀ instr ∈ instructions, match instr with
      | .edge i _ _ => i < 661
      | .gate gate => ∃ g ∈ program, gate = g.toCircuit := by
  intro gates current frame instructions edges
  have check := Geometry.Moves.phase_checked
  rw [Geometry.Moves.phaseEdges,List.forall_mem_append] at check
  have good : ∀ p ∈ edges, Geometry.Moves.CheckedPair p := by
    cases afterScatter
    · exact check.1
    · exact check.2
  refine ⟨good,?_⟩
  apply compiled_valid
  intro g mem
  cases afterScatter <;> simp only [gates,Bool.false_eq_true,ite_false,ite_true,List.mem_append] at mem
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append.mpr mem)))
  · rcases mem with b | c
    · exact List.mem_append_left _ (List.mem_append_right _ b)
    · exact List.mem_append_right _ c

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
  obtain ⟨checked,valid⟩ := invocationPhase_valid w afterScatter
  exact phaseInstructions_stage owner hw hW instructions edges checked valid

open IntegerMultBounds.MathlibTM2.Cover in
noncomputable def labelSpectator {w B K : ℕ}
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    Fin (B*prime^(64*(w*64))*K) :=
  ⟨(z.b.val*prime^(64*(w*64))+(LabelAddress.address g).val)*K+z.after.val, by
      apply LabelShift.pack_lt _ z.after.isLt
      apply LabelShift.pack_lt z.b.isLt
      simpa only [← pow_mul,show w*(64*64) = 64*(w*64) by omega] using (LabelAddress.address g).isLt⟩

open IntegerMultBounds.MathlibTM2.Cover in
/-- At a routed label, the phase reads the same owner bit with the matrix
address, block, and trailing cell packed into its spectator coordinate. -/
theorem phaseRead_label {k w B K : ℕ} (owner : Fin 661 ↪ Fin k) (r : Fin 661)
    (data : Fin k → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    let W := B*prime^(64*(w*64))*K
    let j : Fin W := labelSpectator g z
    let view := fun i => data (owner r) (Fin.cast (copyLabel_volume w B K) i)
    chartRead view g z = phaseRead owner data j r.val (copyActive.symm z.a) := by
  intro W j view
  rw [copyLabel_read]
  let i := FlatCoordinateLayout.index (AffineFieldCoordinates.embed (copyActive.symm z.a)) j
  have pos : i.val = z.a.val*W+j.val := by
    rw [FlatCoordinateLayout.index_val]
    change (copyActive (copyActive.symm z.a)).val*W+j.val = _
    exact congrArg (fun a : Fin ((prime^w)^16) => a.val*W+j.val) (copyActive.apply_symm_apply z.a)
  change M8.RevMachine.ext view (z.a.val*W+j.val) = _
  rw [← pos,M8.RevMachine.ext_cast,M8.RevMachine.ext_apply]
  simp [phaseRead,Copy.extendStored,r.isLt,i]

open IntegerMultBounds.MathlibTM2.Cover in
theorem phaseRead_active {k w B K : ℕ} (owner : Fin 661 ↪ Fin k) (r : Fin 661)
    (data : Fin k → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
    (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    chartRead (fun i => data (owner r) (Fin.cast (copyLabel_volume w B K) i)) g {z with a := copyActive s} =
      phaseRead owner data (labelSpectator g z) r.val s := by
  have eq := phaseRead_label owner r data g {z with a := copyActive s}
  simpa only [Equiv.symm_apply_apply,labelSpectator] using eq

open IntegerMultBounds.MathlibTM2.Cover in
/-- Before chart routing, the physical fanout executes the scatter window
separately on each label, including arbitrary dirty rows. -/
theorem phaseRead_fanout {w B K : ℕ} {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {life : Copy.Lifecycle} (scheduled : life ∈ Copy.lifecycles) {x y}
    (fanout : CopyFanoutEffect n r d life scheduled w B K x y)
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let j := labelSpectator g z
    phaseRead owner y j = scatterWindow (selectedWord w) life (phaseRead owner x j) := by
  intro owner j
  obtain ⟨_,_,other,add⟩ := fanout
  obtain ⟨nodup,noTmp,_,_⟩ := Copy.wellformed life scheduled
  funext i s
  unfold scatterWindow
  by_cases tmp : i = 661
  · subst i
    simp [phaseRead,Copy.extendStored]
  rw [Function.update_of_ne tmp,Copy.addTargets_eq _ nodup noTmp,Function.update_self,Function.update_of_ne tmp]
  by_cases hit : i ∈ life.targets
  · let k : Fin 661 := ⟨i,((Copy.target_bounds life scheduled i hit).2.trans (by decide : 222 < 661))⟩
    let src : Fin 661 := ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    let cell : LabelEntry.Cell (copyLabelLayout w B K) B := {z with a := copyActive s}
    have read := add k hit g cell
    let move := AffineFieldProgram.run (selectedWord w (life.sourceFrame,0))
    have moved : copyActive.symm cell.a = s := copyActive.symm_apply_apply s
    simp only [moved] at read
    rw [ite_eq_left hit]
    exact (phaseRead_active owner k y g z s).symm.trans (read.trans
      (congrArg₂ (· + ·) (phaseRead_active owner k x g z s) (phaseRead_active owner src x g z (move s))))
  · rw [ite_eq_right hit]
    by_cases hi : i < 661
    · let k : Fin 661 := ⟨i,hi⟩
      have keep := other (owner k) (Fin.castSucc_ne_last _) (by
        intro h mem eq
        have same : h.val = i := congrArg Fin.val (owner.injective eq)
        exact hit (same ▸ mem))
      simp only [phaseRead,Copy.extendStored,hi,↓reduceDIte]
      exact congrFun keep _
    · simp [phaseRead,Copy.extendStored,hi]

open IntegerMultBounds.MathlibTM2.Cover in
/-- All nine common-coordinate windows execute the certified COPY word
independently at each row, with one child charge per window. -/
theorem commonScatter_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + 9*engine.time (copyChild w W) hs + 9 ∧
        (∀ x g (z : LabelEntry.Cell (copyLabelLayout w B K) B),
          phaseRead owner (stage.transform x) (labelSpectator g z) =
            Copy.run (selectedFrame w) Copy.lifecycles (phaseRead owner x (labelSpectator g z))) ∧
        ∀ x i, i ≠ Fin.last 142080 → (∀ k, owner k ≠ i) → stage.transform x i = x i := by
  let Life := {l // l ∈ Copy.lifecycles}
  let spec := fun l : Life => commonCopy_stage n r d l.val l.property engine
  let coeff := fun l : Life => (spec l).choose
  refine ⟨(Copy.lifecycles.attach.map coeff).sum,?_⟩
  intro w B K hw hB hK W V hs owner
  let window := fun l : Life => (spec l).choose_spec w B K hw hB hK
  let stage := fun l : Life => (window l).choose
  let compile := fun ls : List Life => SharedBankStage.compile (phaseOwners (N := V)) (by decide) (ls.map stage)
  let child := engine.time (copyChild w W) hs
  have bound (ls : List Life) : (compile ls).cost ≤ (ls.map coeff).sum*V + ls.length*child + ls.length := by
    induction ls with
    | nil => simp [compile,SharedBankStage.compile_cost]
    | cons l ls ih =>
      change (stage l).cost + (compile ls).cost + 1 ≤ _
      have step : (stage l).cost ≤ coeff l*V + child := (window l).choose_spec.2
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [step,ih]
  refine ⟨compile Copy.lifecycles.attach,?_,?_,?_⟩
  · have size : Copy.lifecycles.attach.length = 9 := List.length_attach.trans Copy.copy_count
    have price := bound Copy.lifecycles.attach
    rw [size] at price
    exact price
  · intro x g z
    let read := fun x => phaseRead (w := w) owner x (labelSpectator g z)
    have action (ls : List Life) (x) : read ((compile ls).transform x) =
        (ls.map Subtype.val).foldl (fun b l => scatterWindow (selectedWord w) l b) (read x) := by
      induction ls generalizing x with
      | nil => rfl
      | cons l ls ih =>
        change read ((compile ls).transform ((stage l).transform x)) = _
        rw [ih]
        have step := phaseRead_fanout l.property ((window l).choose_spec.1 x) g z
        change read ((stage l).transform x) = _ at step
        rw [step]
        rfl
    have eq := action Copy.lifecycles.attach x
    rw [List.attach_map_subtype_val] at eq
    exact eq.trans ((modular_scatter w).choose_spec.2.2.2.1 _)
  · intro x i permanent outside
    have keep (ls : List Life) (x) : (compile ls).transform x i = x i := by
      induction ls generalizing x with
      | nil => rfl
      | cons l ls ih =>
        have step := ((window l).choose_spec.1 x).2.2.1 i permanent (fun k _ => outside k)
        exact (ih ((stage l).transform x)).trans step
    exact keep _ _

open IntegerMultBounds.MathlibTM2.Cover in
/-- In the common layout both scalar phases and the intervening fanouts
execute the selected word at every independent physical row. -/
theorem commonInvocation_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
      let bill := fun (gates : List RawGate) (current : ℕ → ℕ) =>
        let code := FramedCircuit.compile (fun i => selectedFrame w (current i))
          (gates.map (Frames.framedGate (selectedFrame w)))
        (code.map (scalarWork V)).sum + ((Frames.edges gates current).map (phaseEdgeBudget owner w W)).sum + code.length
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ bill (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) +
          (C*V + 9*engine.time (copyChild w W) hs + 9) +
          bill (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) + 2 ∧
        (∀ x g (z : LabelEntry.Cell (copyLabelLayout w B K) B),
          phaseRead owner (stage.transform x) (labelSpectator g z) =
            runSelected (selectedFrame w) (selectedWord w) (phaseRead owner x (labelSpectator g z))) ∧
        ∀ x i, i ≠ Fin.last 142080 → (∀ k, owner k ≠ i) → stage.transform x i = x i := by
  obtain ⟨C,scatter⟩ := commonScatter_stage n r d engine
  refine ⟨C,?_⟩
  intro w B K hw hB hK W V owner bill hs
  have hW : 0 < W := Nat.mul_pos (Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _)) hK
  obtain ⟨first,firstCost,firstRead,firstOff⟩ := invocationPhase_stage owner hw hW false
  obtain ⟨last,lastCost,lastRead,lastOff⟩ := invocationPhase_stage owner hw hW true
  obtain ⟨mid,midCost,midRead,midOff⟩ := scatter w B K hw hB hK
  refine ⟨SharedBankStage.compose (SharedBankStage.compose first mid) last,?_,?_,?_⟩
  · change first.cost + mid.cost + 1 + last.cost + 1 ≤ _
    change first.cost ≤ bill (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) at firstCost
    change last.cost ≤ bill (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) at lastCost
    change mid.cost ≤ C*V+9*engine.time (copyChild w W) hs+9 at midCost
    omega
  · intro x g z
    let j := labelSpectator g z
    change phaseRead owner (last.transform (mid.transform (first.transform x))) j = _
    rw [lastRead]
    unfold runSelected
    rw [final_alignment_identity,(modular_scatter w).choose_spec.2.2.2.1]
    apply congrArg (runPhase (selectedWord w) _ _)
    exact (midRead (first.transform x) g z).trans (congrArg (Copy.run (selectedFrame w) Copy.lifecycles) (firstRead x j))
  · intro x i permanent outside
    exact (lastOff _ i outside).trans ((midOff _ i permanent outside).trans (firstOff x i outside))

open IntegerMultBounds.MathlibTM2.Cover RecursiveInterchangeLayout in
noncomputable def scatterRead {w B K : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
    (data : Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2) :
    ℕ → AddressStream (ZMod (prime^w)) :=
  Copy.extendStored fun i s => chartRead (data (ownerTape n r d i)) (g*registerChart w n i.val)
    {z with a := copyActive s}

open IntegerMultBounds.MathlibTM2.Cover in
private theorem scatterRead_window {w B K : ℕ} {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {life : Copy.Lifecycle} (scheduled : life ∈ Copy.lifecycles) {data out}
    (effect : CopyWindowEffect n r d life w B K data out)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    scatterRead n r d g z out = scatterWindow (selectedWord w) life (scatterRead n r d g z data) := by
  obtain ⟨_,other,source,targets⟩ := effect
  obtain ⟨nodup,noTmp,_,_⟩ := Copy.wellformed life scheduled
  have src := (Copy.source_bounds life scheduled).2
  funext i s
  unfold scatterWindow
  by_cases tmp : i = 661
  · subst i
    simp [scatterRead,Copy.extendStored]
  rw [Function.update_of_ne tmp,Copy.addTargets_eq _ nodup noTmp,Function.update_self,Function.update_of_ne tmp]
  by_cases target : i ∈ life.targets
  · have hi := (Copy.target_bounds life scheduled i target).2.trans (by decide : 222 < 661)
    have h := targets i target (g*registerChart w n i) {z with a := copyActive s}
    rw [Matrix.mul_assoc g, mul_eq_one_comm.mp (registerChart_inverse w n i),Matrix.mul_one] at h
    simpa [scatterRead,Copy.extendStored,hi,src,target,Fin.ofNat, Nat.mod_eq_of_lt,Pi.add_apply] using h
  · rw [if_neg target]
    by_cases hi : i < 661
    · by_cases eq : i = life.source
      · subst i
        have h := congrFun (source (g*registerChart w n life.source)) {z with a := copyActive s}
        simpa [scatterRead,Copy.extendStored,src,Fin.ofNat,Nat.mod_eq_of_lt] using h
      · let k := ownerTape n r d ⟨i,hi⟩
        have distinct (j : ℕ) (hj : j < 661) (ne : i ≠ j) : k ≠ ownerTape n r d (Fin.ofNat 661 j) := by
          intro same
          have he := congrArg Fin.val (ownerTape_injective n r d same)
          exact ne (he.trans (Nat.mod_eq_of_lt hj))
        have keep := other k (Fin.castSucc_ne_last _) (distinct _ src eq) (by
          intro mem
          obtain ⟨j,hj,same⟩ := List.mem_map.mp mem
          exact distinct j ((Copy.target_bounds life scheduled j hj).2.trans (by decide)) (fun e => target (e ▸ hj)) same.symm)
        simp only [scatterRead,Copy.extendStored,hi,↓reduceDIte]
        exact congrArg (fun x => chartRead x (g*registerChart w n i) {z with a := copyActive s}) keep
    · simp [scatterRead,Copy.extendStored,hi]

open IntegerMultBounds.MathlibTM2.Cover in
theorem scatterRead_schedule {w B K : ℕ} {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {lives : List Copy.Lifecycle} (scheduled : ∀ life ∈ lives, life ∈ Copy.lifecycles) {data out}
    (effect : CopyScheduleEffect n r d w B K lives data out)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    scatterRead n r d g z out = lives.foldl (fun b l => scatterWindow (selectedWord w) l b)
      (scatterRead n r d g z data) := by
  induction lives generalizing data with
  | nil => exact congrArg (scatterRead n r d g z) effect.symm
  | cons l ls ih =>
    obtain ⟨mid,step,rest⟩ := effect
    rw [ih (fun a h => scheduled a (List.mem_cons_of_mem _ h)) rest,
      scatterRead_window (scheduled _ List.mem_cons_self) step]
    rfl

open IntegerMultBounds.MathlibTM2.Cover in
theorem scatterRead_endpoint {w B K : ℕ} {n : Fin 9} {r : Fin 32} {d : Fin 5} {data out}
    (effect : CopyScheduleEffect n r d w B K Copy.lifecycles data out)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    let frame := fun i => selectedFrame w (Frames.beforeScatter i)
    let stored := FramedCircuit.decode frame (scatterRead n r d g z data)
    ∀ i : Fin 661, scatterRead n r d g z out i.val =
      frame i.val (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) stored i.val) := by
  intro frame stored i
  let live := fun j : Fin 661 => stored j.val
  have full : Copy.extendStored live = stored := by
    funext j
    by_cases h : j < 661
    · simp [Copy.extendStored,h,live]
    · simp [stored,FramedCircuit.decode,scatterRead,Copy.extendStored,h]
  have encoded : FramedCircuit.encode frame (Copy.extendStored live) = scatterRead n r d g z data := by
    rw [full,FramedCircuit.encode_decode]
  have h := Copy.decoded_scatter (selectedFrame w) live i
  change Copy.run (selectedFrame w) Copy.lifecycles (FramedCircuit.encode frame (Copy.extendStored live)) i.val = _ at h
  rw [encoded,full] at h
  rw [scatterRead_schedule (fun _ h => h) effect,(modular_scatter w).choose_spec.2.2.2.1]
  exact h

open IntegerMultBounds.MathlibTM2.Cover in
private theorem scatterRead_flat {w B K : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
    (data : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) (i : Fin 661) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let view := fun k t => data k (Fin.cast (copyLabel_volume w B K) t)
    scatterRead n r d g z view i.val =
      phaseRead owner data (labelSpectator (g*registerChart w n i.val) z) i.val := by
  intro owner view
  funext s
  let G := g*registerChart w n i.val
  let cell : LabelEntry.Cell (copyLabelLayout w B K) B := {z with a := copyActive s}
  change (if h : i.val < 661 then _ else (0 : AddressStream (ZMod (prime^w)))) s = _
  rw [dite_eq_left i.isLt]
  have h := @phaseRead_label 142081 w B K owner i data G cell
  have cancel : (copyActive (Q := prime^w)).symm cell.a = s := (copyActive (Q := prime^w)).symm_apply_apply s
  change chartRead (view (owner i)) G cell = phaseRead owner data (labelSpectator G z) i.val s
  dsimp only at h
  have spectator : labelSpectator G cell = labelSpectator G z := by
    apply Fin.ext
    simp only [labelSpectator,cell]
  rw [spectator,cancel] at h
  exact h

/-- Interpret all nine COPY windows on a bank indexed by a common matrix
label. Each target reads its sources at their relative register charts. -/
noncomputable def labelScatter {w : ℕ} (n : Fin 9)
    (bank : Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) → ℕ → AddressStream (ZMod (prime^w)))
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) : ℕ → AddressStream (ZMod (prime^w)) :=
  let frame := fun i => selectedFrame w (Frames.beforeScatter i)
  Copy.extendStored fun i =>
    let base := g*(registerChart w n i.val).transpose
    let stored := Copy.extendStored fun j : Fin 661 => bank (base*registerChart w n j.val) j.val
    frame i.val (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit)
      (FramedCircuit.decode frame stored) i.val)

/-- At a target, decoding the physical scatter reads each incident helper
at the label obtained from that target's chart and the helper's chart. -/
theorem labelScatter_sum {w : ℕ} (n : Fin 9)
    (x : Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) → ℕ → AddressStream (ZMod (prime^w)))
    (g) (i : Fin 661) :
    let frame := fun j => selectedFrame w (Frames.beforeScatter j)
    let base := g*(registerChart w n i.val).transpose
    FramedCircuit.decode frame (labelScatter n (fun h => FramedCircuit.encode frame (x h)) g) i.val =
      x g i.val + ((Copy.lifecycles.filter (fun l => i.val ∈ l.targets)).map
        (fun l => x (base*registerChart w n l.source) l.source)).sum := by
  intro frame base
  let stored := fun j : Fin 661 => x (base*registerChart w n j.val) j.val
  have decoded : FramedCircuit.decode frame (Copy.extendStored (fun j : Fin 661 =>
      FramedCircuit.encode frame (x (base*registerChart w n j.val)) j.val)) = Copy.extendStored stored := by
    funext j
    by_cases low : j < 661 <;> simp [Copy.extendStored,FramedCircuit.decode,FramedCircuit.encode,low,stored]
  simp only [labelScatter,Copy.extendStored,dite_eq_left i.isLt,FramedCircuit.decode]
  change (frame i.val).symm (frame i.val (FramedCircuit.moduleRun _ _ i.val)) = _
  rw [LinearEquiv.symm_apply_apply]
  change FramedCircuit.moduleRun _ (FramedCircuit.decode frame (Copy.extendStored _)) i.val = _
  rw [decoded,← Copy.logical_scatter_streams,Copy.logicalRun_sum _ (fun _ h => h)]
  have cancel : base*registerChart w n i.val = g := by
    change g*(registerChart w n i.val).transpose*registerChart w n i.val = g
    rw [Matrix.mul_assoc,registerChart_inverse,Matrix.mul_one]
  simp only [Copy.extendStored,dite_eq_left i.isLt,stored,cancel]
  apply congrArg (x g i.val + ·)
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  have low := (Copy.source_bounds l (List.mem_filter.mp hl).1).2
  simp [low]

/-- Subtracting the common-label result cancels the target's dirty value.
Only incident helper differences remain. -/
theorem labelScatter_difference {w : ℕ} (n : Fin 9)
    (x : Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) → ℕ → AddressStream (ZMod (prime^w)))
    (g) (i : Fin 661) (high : ∀ j, 661 ≤ j → x g j = 0) :
    let frame := fun j => selectedFrame w (Frames.beforeScatter j)
    let base := g*(registerChart w n i.val).transpose
    FramedCircuit.decode frame (labelScatter n (fun h => FramedCircuit.encode frame (x h)) g) i.val -
      FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) (x g) i.val =
      ((Copy.lifecycles.filter (fun l => i.val ∈ l.targets)).map
        (fun l => x (base*registerChart w n l.source) l.source - x g l.source)).sum := by
  intro frame base
  let stored := fun j : Fin 661 => x g j.val
  have bounded : x g = Copy.extendStored stored := by
    funext j
    by_cases low : j < 661 <;> simp [Copy.extendStored,stored,low]
    exact high j (by omega)
  have localRead := (Copy.logical_scatter_streams stored i).symm.trans
    (Copy.logicalRun_sum _ (fun _ h => h) _ _)
  rw [← bounded] at localRead
  rw [labelScatter_sum,localRead,add_sub_add_left_eq_sub]
  generalize (Copy.lifecycles.filter _) = windows
  induction windows with
  | nil => simp
  | cons l rest ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [← ih]
    abel

/-- Scatter never writes a source or helper, even when the register charts
select different labels for all of its incoming terms. -/
theorem labelScatter_other {w : ℕ} (n : Fin 9) (bank) (g) (i : Fin 661)
    (outside : i.val < 111 ∨ 222 ≤ i.val) : labelScatter (w := w) n bank g i.val = bank g i.val := by
  simp only [labelScatter,Copy.extendStored,dite_eq_left i.isLt]
  rw [FramedCircuit.moduleRun_preserves]
  · simp only [FramedCircuit.decode,LinearEquiv.apply_symm_apply,Copy.extendStored,dite_eq_left i.isLt,
      Matrix.mul_assoc,registerChart_inverse,Matrix.mul_one]
  · intro gate mem
    obtain ⟨raw,scheduled,rfl⟩ := List.mem_map.mp mem
    have h := of_decide_eq_true (List.all_eq_true.mp scatter_target_range raw scheduled)
    change raw.target ≠ i.val
    omega

private theorem run_shift {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (gs : List RawGate) (delta : ℕ → E)
    (zero : ∀ g ∈ gs, ∀ j ∈ g.sources, delta j = 0) (x : ℕ → E) :
    FramedCircuit.moduleRun (gs.map RawGate.toCircuit) (x+delta) =
      FramedCircuit.moduleRun (gs.map RawGate.toCircuit) x + delta := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons,FramedCircuit.moduleRun_cons]
    have terms : (g.toCircuit.terms.map (fun p => p.2 • (x+delta) p.1)) =
        g.toCircuit.terms.map (fun p => p.2 • x p.1) := by
      simp only [RawGate.toCircuit,List.map_map]
      apply List.map_congr_left
      intro j mem
      simp [Pi.add_apply,zero g (by simp) j mem]
    have gate : FramedCircuit.moduleGate g.toCircuit (x+delta) =
        FramedCircuit.moduleGate g.toCircuit x + delta := by
      funext j
      by_cases eq : j = g.target
      · subst j
        simp only [FramedCircuit.moduleGate,terms,show g.target = g.toCircuit.target from rfl,
          Function.update_self,Pi.add_apply]
        have h := congrArg List.sum terms
        simp only [Pi.add_apply] at h
        rw [h]
        abel
      · simp only [FramedCircuit.moduleGate,Function.update_of_ne (show j ≠ g.toCircuit.target from eq),Pi.add_apply]
    rw [gate,ih (fun a mem => zero a (by simp [mem]))]

/-- Every discrepancy introduced by chart-dependent fanout on the 111
target ports passes through B and C unchanged, including on dirty banks. -/
theorem afterScatter_shift {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (x delta : ℕ → E) (outside : ∀ j, j < 111 ∨ 222 ≤ j → delta j = 0) :
    FramedCircuit.moduleRun ((sectionB++sectionC).map RawGate.toCircuit) (x+delta) =
      FramedCircuit.moduleRun ((sectionB++sectionC).map RawGate.toCircuit) x + delta := by
  exact run_shift _ delta (fun g mem j hj => outside j (afterScatter_source_range g mem j hj)) x

/-- Reading each output at its register chart turns the physical scatter into
one framed scalar word on the registers of a common base label. -/
theorem labelScatter_at_chart {w : ℕ} (n : Fin 9)
    (bank : Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) → ℕ → AddressStream (ZMod (prime^w)))
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (i : Fin 661) :
    let frame := fun j => selectedFrame w (Frames.beforeScatter j)
    let stored := Copy.extendStored fun j : Fin 661 => bank (g*registerChart w n j.val) j.val
    labelScatter n bank (g*registerChart w n i.val) i.val =
      frame i.val (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit)
        (FramedCircuit.decode frame stored) i.val) := by
  have cancel : g*registerChart w n i.val*(registerChart w n i.val).transpose = g := by
    rw [Matrix.mul_assoc,mul_eq_one_comm.mp (registerChart_inverse w n i.val),Matrix.mul_one]
  simp only [labelScatter,Copy.extendStored,dite_eq_left i.isLt,cancel]

open IntegerMultBounds.MathlibTM2.Cover in
theorem labelScatter_read {w B K : ℕ} {n : Fin 9} {r : Fin 32} {d : Fin 5}
    (data out : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (effect : CopyScheduleEffect n r d w B K Copy.lifecycles
      (fun k t => data k (Fin.cast (copyLabel_volume w B K) t))
      (fun k t => out k (Fin.cast (copyLabel_volume w B K) t)))
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    phaseRead owner out (labelSpectator g z) =
      labelScatter n (fun h => phaseRead owner data (labelSpectator h z)) g := by
  intro owner
  funext i
  by_cases hi : i < 661
  · let j : Fin 661 := ⟨i,hi⟩
    let base := g*(registerChart w n i).transpose
    let view := fun (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) k t =>
      x k (Fin.cast (copyLabel_volume w B K) t)
    have inputs : scatterRead n r d base z (view data) = Copy.extendStored (fun a : Fin 661 =>
        phaseRead owner data (labelSpectator (base*registerChart w n a.val) z) a.val) := by
      funext a
      by_cases ha : a < 661
      · simpa only [Copy.extendStored,ha,↓reduceDIte] using scatterRead_flat n r d base z data ⟨a,ha⟩
      · simp [scatterRead,Copy.extendStored,ha]
    have h := scatterRead_endpoint effect base z j
    change scatterRead n r d base z (view out) i = _ at h
    rw [show scatterRead n r d base z (view out) i = _ from scatterRead_flat n r d base z out j] at h
    have cancel : base*registerChart w n j.val = g := by
      change g*(registerChart w n i).transpose*registerChart w n i = g
      rw [Matrix.mul_assoc,registerChart_inverse,Matrix.mul_one]
    rw [cancel] at h
    change _ = selectedFrame w (Frames.beforeScatter i) (FramedCircuit.moduleRun _
      (FramedCircuit.decode _ (scatterRead n r d base z (view data))) i) at h
    rw [inputs] at h
    simpa only [labelScatter,Copy.extendStored,hi,↓reduceDIte] using h
  · simp [labelScatter,phaseRead,Copy.extendStored,hi]

theorem phaseLogicalRead (w : ℕ) (gates : List RawGate) (current : ℕ → ℕ)
    (checked : ∀ p ∈ Frames.edges gates current, Geometry.Moves.CheckedPair p)
    (input : ℕ → AddressStream (ZMod (prime^w))) :
    let frame := selectedFrame w
    runPhase (selectedWord w) (FramedCircuit.compile (fun i => frame (current i)) (gates.map (Frames.framedGate frame)))
        (Frames.edges gates current) input =
      FramedCircuit.encode (fun i => frame (Frames.run gates current i))
        (FramedCircuit.moduleRun (gates.map RawGate.toCircuit)
          (FramedCircuit.decode (fun i => frame (current i)) input)) := by
  intro frame
  rw [runPhase_eq _ frame (modular_scatter w).choose_spec.1 _ _ (Frames.compile_pairs ..) checked]
  simpa only [FramedCircuit.encode_decode] using
    Frames.compile_semantics frame gates current (FramedCircuit.decode (fun i => frame (current i)) input)

open RecursiveInterchangeLayout (Descriptor volume) in
theorem flatCopyStage {k V : ℕ} {v : Descriptor} (size : volume prime v = V)
    (effect : (Fin k → Fin (volume prime v) → ZMod 2) → (Fin k → Fin (volume prime v) → ZMod 2) → Prop)
    (budget : ℕ) (stage : SharedBankStage.Stage _ k prime (copyOwners (v := v)))
    (acts : ∀ data, effect data (stage.transform data)) (bill : stage.cost ≤ budget) :
    let view := fun (data : Fin k → Fin V → ZMod 2) r i => data r (Fin.cast size i)
    ∃ flat : SharedBankStage.Stage _ k prime (phaseOwners (N := V)), flat.cost ≤ budget ∧
      ∀ data, effect (view data) (view (flat.transform data)) := by
  subst V
  intro view
  have same : @phaseOwners k (volume prime v) = copyOwners (v := v) := by
    funext data
    apply congrArg₂ Tapes.mk
    · rfl
    · funext r
      exact (sourceWord_cast (v := v) rfl (data r)).symm
  rw [same]
  exact ⟨stage,bill,acts⟩

open Cover M8.RevMachine in
private theorem ownerLabelRead {w B K : ℕ} (G : LabelPadding.Label 64 w)
    (z : LabelEntry.Cell (copyLabelLayout w B K) B) (s : Swap.Shear.State (Fin 8) (ZMod (prime^w)))
    (a : Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) :
    chartRead (fun i => a (i.cast (copyLabel_volume w B K))) G {z with a := copyActive s} =
      a (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (labelSpectator G z)) := by
  let j := labelSpectator G z
  let idx := FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j
  have val : idx.val = (copyActive s).val*(B*prime^(64*(w*64))*K)+j.val :=
    FlatCoordinateLayout.index_val _ _
  rw [copyLabel_read]
  change ext (fun i => a (i.cast _)) ((copyActive s).val*(B*prime^(64*(w*64))*K)+j.val) = _
  rw [← val,ext_cast,ext_apply]

open Cover RecursiveInterchangeLayout M8.RevMachine in
/-- The direct helper-chart transition on a permanent physical owner. It
moves the label inside the spectator record, preserving every active field
and all words on the other owners. -/
theorem helperWindow_ownerStage [M8.Machine.Net] {T : ℕ} (io : Fin T)
    (previous destination : Option (Fin 9 × Fin 439)) :
    ∃ C : ℕ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ T prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + 63*LeafCore.coreCost V (w*64) ∧
        ∀ x, (∀ t, t ≠ io → stage.transform x t = x t) ∧
        ∀ (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
          (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))),
          let addr := fun j => FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j
          stage.transform x io (addr (labelSpectator (helperLabel w destination g) z)) =
            x io (addr (labelSpectator (helperLabel w previous g) z)) := by
  classical
  obtain ⟨block,C,leading,run⟩ := helperLabelTransition io previous destination
  refine ⟨C,?_⟩
  intro w B K hw hB hK W V
  let v := copyLabelLayout w B K
  have size : volume prime v = V := copyLabel_volume w B K
  have positive : v.Positive := by
    have hp := Shared50ModularControl.prime_prime.pos
    simp only [v,Descriptor.Positive,copyLabelLayout]
    exact ⟨by positivity,by decide,by positivity,by decide,hK⟩
  let d := M8.Stage2Machine.Straight.words (LabelSchedule.base v w)
  let result := fun x : Fin T → Fin (volume prime v) → ZMod 2 =>
    run v w B hw hB rfl positive (copyOwners x) (x io) rfl rfl
  let next := fun x => Function.update x io (result x).choose
  let bank := fun x : Fin T → Fin (volume prime v) → ZMod 2 => SharedBankStageInput.raw (LabelCall.bank (copyOwners (v := v) x) v d) block.tapes
  let slots := fun i : Fin T => block.slots (Fin.castAdd 24 i)
  let routed : SharedBankStage.Stage _ T prime (copyOwners (v := v)) := {
    tapes := block.tapes, states := block.states, program := block.program, transform := next,
    input := bank, output := fun x => bank (next x), slots := slots,
    slots_injective := block.slots_injective.comp (Fin.castAdd_injective T 24),
    metadata := SharedBank.strip (bank 0) slots, cost := C*volume prime v + 63*LeafCore.coreCost (volume prime v) (w*64),
    input_payload := fun x => copyRoute_payload block leading _ v d,
    output_payload := fun x => copyRoute_payload block leading _ v d,
    strip_input := fun x => routePrivate block leading _ _ v d,
    realizes := fun x => by
      have step := (result x).choose_spec.2
      have updated : SharedPlacementAlphabet.setTape (copyOwners x) io
          (M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (result x).choose) 0 = copyOwners (next x) := by
        apply congrArg₂ Tapes.mk <;> funext t <;> by_cases eqn : t = io <;> simp [copyOwners,next,eqn]
      rw [updated] at step
      exact step }
  let effect := fun (a b : Fin T → Fin (volume prime v) → ZMod 2) =>
    (∀ t, t ≠ io → b t = a t) ∧ ∀ g : LabelPadding.Label 64 w,
      chartRead (B := B) (b io) (helperLabel w destination g) =
      chartRead (a io) (helperLabel w previous g)
  obtain ⟨stage,bill,acts⟩ := flatCopyStage size effect routed.cost routed (fun x =>
    ⟨fun t off => Function.update_of_ne off _ _,by
      change ∀ g, chartRead (B := B) (next x io) _ = _
      simp only [next,Function.update_self]
      exact (result x).choose_spec.1⟩) le_rfl
  refine ⟨stage,by simpa only [routed,size] using bill,?_⟩
  intro x
  obtain ⟨idle,read⟩ := acts x
  constructor
  · intro t off
    funext i
    exact congrFun (idle t off) (i.cast size.symm)
  · intro g z s addr
    let cell : LabelEntry.Cell v B := {z with a := copyActive s}
    exact (ownerLabelRead _ z s _).symm.trans ((congrFun (read g) cell).trans (ownerLabelRead _ z s _))

open Cover M8.RevMachine in
/-- Change the helper charts that differ at an invocation boundary. Each
selected owner is routed once, from its recorded previous chart. -/
theorem helperWindow_batch [M8.Machine.Net] {ι : Type} (owner : ι → Fin 142081)
    (inj : Function.Injective owner) (previous destination : ι → Option (Fin 9 × Fin 439))
    (hs : List ι) (unique : hs.Nodup) :
    ∃ C : ℕ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + hs.length*(63*LeafCore.coreCost V (w*64)+1) ∧
        ∀ x, (∀ t, t ∉ hs.map owner → stage.transform x t = x t) ∧
        ∀ h ∈ hs, ∀ (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
          (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))),
          let addr := fun j => FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j
          let old := previous h
          stage.transform x (owner h) (addr (labelSpectator (helperLabel w (destination h) g) z)) =
            x (owner h) (addr (labelSpectator (helperLabel w old g) z)) := by
  classical
  induction hs with
  | nil =>
    refine ⟨0,fun w B K _ _ _ => ⟨SharedBankStage.identity _ (by decide),by simp [SharedBankStage.identity],?_⟩⟩
    intro x
    exact ⟨fun _ _ => rfl,fun _ hit => False.elim (List.not_mem_nil hit)⟩
  | cons h hs ih =>
    obtain ⟨fresh,nd⟩ := List.nodup_cons.mp unique
    obtain ⟨P,one⟩ := helperWindow_ownerStage (owner h) (previous h) (destination h)
    obtain ⟨Q,rest⟩ := ih nd
    refine ⟨P+Q,?_⟩
    intro w B K hw hb hk W V
    obtain ⟨A,ca,a⟩ := one w B K hw hb hk
    obtain ⟨D,cd,b⟩ := rest w B K hw hb hk
    refine ⟨SharedBankStage.compose A D,?_,?_⟩
    · change A.cost+D.cost+1 ≤ _
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      dsimp only [V,W]
      omega
    · intro x
      obtain ⟨idle,read⟩ := a x
      obtain ⟨idle',read'⟩ := b (A.transform x)
      constructor
      · intro t off
        simp only [List.map_cons,List.mem_cons,not_or] at off
        exact (idle' t off.2).trans (idle t off.1)
      · intro k hit g z s addr old
        change D.transform (A.transform x) _ _ = _
        rcases List.mem_cons.mp hit with eqn | mem
        · subst k
          rw [idle' _ (by simpa [List.mem_map,inj.eq_iff] using fresh)]
          exact read g z s
        · exact (read' k mem g z s).trans (congrFun (idle _ (fun eqn => fresh (inj eqn ▸ mem))) _)

open Cover M8.RevMachine in
/-- Prepare every helper for its next invocation, skipping charts already in place. -/
theorem prepareHelperWindows [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (previous : Fin 439 → Option (Fin 9 × Fin 439)) :
    let owner := fun h : Fin 439 => ownerTape n r d ⟨222+h.val,by omega⟩
    let hs := (List.finRange 439).filter (fun h => previous h != some (n,h))
    ∃ C : ℕ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + hs.length*(63*LeafCore.coreCost V (w*64)+1) ∧
        ∀ x, (∀ t, t ∉ hs.map owner → stage.transform x t = x t) ∧
        ∀ h : Fin 439, ∀ (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
          (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))),
          let addr := fun j => FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j
          let old := previous h
          stage.transform x (owner h) (addr (labelSpectator (g*(registerChart w n (222+h.val)).transpose) z)) =
            x (owner h) (addr (labelSpectator (helperLabel w old g) z)) := by
  intro owner hs
  have unique : hs.Nodup := (List.nodup_finRange 439).filter _
  have inj : Function.Injective owner := by
    intro h k eqn
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ownerTape_injective n r d eqn)))
  obtain ⟨C,run⟩ := helperWindow_batch owner inj previous (fun h => some (n,h)) hs unique
  refine ⟨C,?_⟩
  intro w B K hw hb hk W V
  obtain ⟨stage,cost,act⟩ := run w B K hw hb hk
  refine ⟨stage,cost,?_⟩
  intro x
  obtain ⟨idle,read⟩ := act x
  refine ⟨idle,?_⟩
  intro h g z s addr old
  by_cases hit : h ∈ hs
  · exact read h hit g z s
  · have same : previous h = some (n,h) := by simpa [hs] using hit
    have off : owner h ∉ hs.map owner := by
      rintro mem
      obtain ⟨k,hk,eqn⟩ := List.mem_map.mp mem
      have eqh := congrArg Fin.val (ownerTape_injective n r d eqn)
      exact hit ((Fin.ext (Nat.add_left_cancel eqh) : k = h) ▸ hk)
    rw [idle _ off]
    simp only [old,same,helperLabel]

/-- Chart record after a replica/class invocation. Each helper owner takes
the chart of its scheduled register; other owners retain their record. -/
noncomputable def helperChartsAfter (n : Fin 9) (run : Fin 32 × Fin 5)
    (before : Fin 142081 → Option (Fin 9 × Fin 439)) (t : Fin 142081) : Option (Fin 9 × Fin 439) := by
  classical
  exact if hit : ∃ h : Fin 439, ownerTape n run.1 run.2 ⟨222+h.val,by omega⟩ = t
    then some (n,hit.choose) else before t

/-- With an uncharted incoming bank, precisely the owners absent from the
entire prefix are still read at the original label. -/
theorem helperCharts_unvisited (n : Fin 9) (runs : List (Fin 32 × Fin 5)) (t : Fin 142081) :
    (runs.foldl (fun chart p => helperChartsAfter n p chart) (fun _ => none)) t = none ↔
      ∀ p ∈ runs, ∀ h : Fin 439, ownerTape n p.1 p.2 ⟨222+h.val,by omega⟩ ≠ t := by
  suffices more : ∀ chart, (runs.foldl (fun a p => helperChartsAfter n p a) chart) t = none ↔
      chart t = none ∧ ∀ p ∈ runs, ∀ h : Fin 439, ownerTape n p.1 p.2 ⟨222+h.val,by omega⟩ ≠ t by
    simpa using more (fun _ => none)
  induction runs with
  | nil => simp
  | cons p ps ih =>
    intro chart
    rw [List.foldl_cons,ih]
    by_cases hit : ∃ h : Fin 439, ownerTape n p.1 p.2 ⟨222+h.val,by omega⟩ = t
    · rw [helperChartsAfter,dif_pos hit]
      constructor
      · rintro ⟨eqn,_⟩; contradiction
      · rintro ⟨_,off⟩
        exact False.elim (off p List.mem_cons_self hit.choose hit.choose_spec)
    · simp only [helperChartsAfter,dif_neg hit,List.forall_mem_cons]
      push_neg at hit
      simp [hit]

/-- The last scheduled use of an owner determines its current helper chart. -/
theorem helperChart_lastUse (n : Fin 9) (pre post : List (Fin 32 × Fin 5))
    (run : Fin 32 × Fin 5) (h : Fin 439) (initial : Fin 142081 → Option (Fin 9 × Fin 439)) :
    let t := ownerTape n run.1 run.2 ⟨222+h.val,by omega⟩
    (∀ p ∈ post, ∀ k : Fin 439, ownerTape n p.1 p.2 ⟨222+k.val,by omega⟩ ≠ t) →
    ((pre ++ run :: post).foldl (fun chart p => helperChartsAfter n p chart) initial) t = some (n,h) := by
  intro t untouched
  rw [List.foldl_append,List.foldl_cons]
  have keep (chart : Fin 142081 → Option (Fin 9 × Fin 439)) :
      (post.foldl (fun chart p => helperChartsAfter n p chart) chart) t = chart t := by
    induction post generalizing chart with
    | nil => rfl
    | cons p ps ih =>
      rw [List.foldl_cons,ih (fun q mem => untouched q (List.mem_cons_of_mem _ mem))]
      exact dif_neg (fun ⟨k,eqn⟩ => untouched p List.mem_cons_self k eqn)
  rw [keep]
  have hit : ∃ k : Fin 439, ownerTape n run.1 run.2 ⟨222+k.val,by omega⟩ = t := ⟨h,rfl⟩
  have eqn := congrArg Fin.val (ownerTape_injective n run.1 run.2 hit.choose_spec)
  have same : hit.choose = h := Fin.ext (Nat.add_left_cancel eqn)
  rw [helperChartsAfter,dif_pos hit,same]

open Cover M8.RevMachine in
/-- The physical chart preparation transports the whole bank between its
incoming and outgoing chart records, at the cost of the changed owners. -/
theorem helperChartsAfter_stage [M8.Machine.Net] (n : Fin 9) (run : Fin 32 × Fin 5)
    (before : Fin 142081 → Option (Fin 9 × Fin 439)) :
    let owner := fun h : Fin 439 => ownerTape n run.1 run.2 ⟨222+h.val,by omega⟩
    let changed := (List.finRange 439).filter (fun h => before (owner h) != some (n,h))
    ∃ C : ℕ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let addr := fun (c : Option (Fin 9 × Fin 439)) (g : LabelPadding.Label 64 w)
        (z : LabelEntry.Cell (copyLabelLayout w B K) B) (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) =>
        FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
          (labelSpectator (helperLabel w c g) z)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + changed.length*(63*LeafCore.coreCost V (w*64)+1) ∧
        ∀ x t, (t ∉ changed.map owner → stage.transform x t = x t) ∧
          ∀ g z s, stage.transform x t (addr (helperChartsAfter n run before t) g z s) =
            x t (addr (before t) g z s) := by
  classical
  intro owner changed
  obtain ⟨C,prepare⟩ := prepareHelperWindows n run.1 run.2 (before ∘ owner)
  refine ⟨C,?_⟩
  intro w B K hw hb hk W V addr
  obtain ⟨stage,cost,act⟩ := prepare w B K hw hb hk
  refine ⟨stage,cost,?_⟩
  intro x t
  obtain ⟨off,read⟩ := act x
  refine ⟨off t,?_⟩
  by_cases hit : ∃ h : Fin 439, owner h = t
  · have slot : helperChartsAfter n run before t = some (n,hit.choose) := dif_pos hit
    rw [slot]
    have atOwner (h : Fin 439) (t : Fin 142081) (eqn : owner h = t) :
        ∀ g z s, stage.transform x t (addr (some (n,h)) g z s) = x t (addr (before t) g z s) := by
      subst t
      exact read h
    exact atOwner _ _ hit.choose_spec
  · have miss : t ∉ changed.map owner := by
      rintro ht
      obtain ⟨h,_,eqn⟩ := List.mem_map.mp ht
      exact hit ⟨h,eqn⟩
    rw [off t miss,show helperChartsAfter n run before t = before t from dif_neg hit]
    exact fun _ _ _ => rfl

noncomputable def helperChangeCount (n : Fin 9) :
    List (Fin 32 × Fin 5) → (Fin 142081 → Option (Fin 9 × Fin 439)) → ℕ
  | [], _ => 0
  | p :: ps, before =>
    ((List.finRange 439).filter (fun h => before (ownerTape n p.1 p.2 ⟨222+h.val,by omega⟩) != some (n,h))).length +
      helperChangeCount n ps (helperChartsAfter n p before)

open Cover in
/-- A chart preparation followed by the supplied invocation at every scheduled
run. The intermediate bank is the physical input to that invocation. -/
def PreparedHelperTrace (n : Fin 9) (w B K : ℕ)
    (invoke : Fin 32 × Fin 5 → (Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) →
      (Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)) :
    List (Fin 32 × Fin 5) → (Fin 142081 → Option (Fin 9 × Fin 439)) → (Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) →
    (Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) → Prop
  | [], _, x, y => x = y
  | p :: ps, before, x, y =>
    let after := helperChartsAfter n p before
    let addr := fun c (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
      (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) => FlatCoordinateLayout.index
        (AffineFieldCoordinates.embed s) (labelSpectator (helperLabel w c g) z)
    ∃ ready, (∀ t, (∀ h : Fin 439, ownerTape n p.1 p.2 ⟨222+h.val,by omega⟩ ≠ t) → ready t = x t) ∧
      (∀ t g z s, ready t (addr (after t) g z s) = x t (addr (before t) g z s)) ∧
      PreparedHelperTrace n w B K invoke ps after (invoke p ready) y

open M8.RevMachine in
theorem preparedHelperSchedule [M8.Machine.Net] (n : Fin 9) (ps : List (Fin 32 × Fin 5))
    (before : Fin 142081 → Option (Fin 9 × Fin 439)) :
    ∃ C : ℕ, ∀ w B K : ℕ, 0 < w → 0 < B → 0 < K →
      let V := (prime^w)^16*(B*prime^(64*(w*64))*K)
      ∀ calls : Fin 32 × Fin 5 → SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + helperChangeCount n ps before*(63*LeafCore.coreCost V (w*64)+1) +
          (ps.map (fun p => (calls p).cost)).sum + 2*ps.length ∧
        ∀ x, PreparedHelperTrace n w B K (fun p => (calls p).transform) ps before x (stage.transform x) := by
  induction ps generalizing before with
  | nil =>
    refine ⟨0,fun w B K _ _ _ calls => ⟨SharedBankStage.identity _ (by decide),?_,fun x => rfl⟩⟩
    simp [SharedBankStage.identity,helperChangeCount]
  | cons p ps ih =>
    obtain ⟨P,prepare⟩ := helperChartsAfter_stage n p before
    obtain ⟨Q,rest⟩ := ih (helperChartsAfter n p before)
    refine ⟨P+Q,?_⟩
    intro w B K hw hb hk V calls
    obtain ⟨A,ca,read⟩ := prepare w B K hw hb hk
    obtain ⟨D,cd,tail⟩ := rest w B K hw hb hk calls
    refine ⟨SharedBankStage.compose (SharedBankStage.compose A (calls p)) D,?_,?_⟩
    · change A.cost + (calls p).cost + 1 + D.cost + 1 ≤ _
      simp only [helperChangeCount,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.mul_add]
      dsimp only [V]
      simp only [Nat.mul_add] at ca cd
      omega
    · intro x
      refine ⟨A.transform x,?_,fun t => (read x t).2,tail _⟩
      intro t off
      apply (read x t).1
      rintro hit
      obtain ⟨h,_,eqn⟩ := List.mem_map.mp hit
      exact off h eqn

-- The explicit entry and return chart programs are available in commit 1b183c9b.
/-- Read each permanent register in its own invocation chart. -/
noncomputable def chartedPhaseRead {w B K : ℕ} (n : Fin 9) (owner : Fin 661 ↪ Fin 142081)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) :=
  Copy.extendStored fun j => phaseRead owner x (labelSpectator (g*registerChart w n j.val) z) j.val

private theorem chartedPhase_encode {w B K : ℕ} (n : Fin 9) (owner : Fin 661 ↪ Fin 142081)
    (x) (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) :
    let stored := fun j : Fin 661 => (selectedFrame w (Frames.initialRefs j.val)).symm (chartedPhaseRead n owner x g z j.val)
    FramedCircuit.encode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (Copy.extendStored stored) = chartedPhaseRead n owner x g z := by
  intro stored
  funext j
  by_cases hj : j < 661
  · simp only [FramedCircuit.encode,Frames.snapshot,Copy.extendStored,stored,hj,ite_true,↓reduceDIte,
      LinearEquiv.apply_symm_apply]
  · simp [FramedCircuit.encode,Copy.extendStored,chartedPhaseRead,hj]

open Matrix IntegerMultBounds.Swap.Modular in
/-- Read the actual charted invocation at a corrected target address.
The input on this label can be any dirty bank. -/
theorem chartedTarget_read {n : Fin 9} {w B K : ℕ} {owner : Fin 661 ↪ Fin 142081} {x y}
    (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B)
    (run : chartedPhaseRead n owner y g z =
      runSelected (selectedFrame w) (selectedWord w) (chartedPhaseRead n owner x g z)) (t : Fin 111) :
    let R := ZMod (prime^w)
    let P := translatedPortProjector R (4:R)⁻¹ t
    let V := reduce (prime^w) (selectedProjector ⟨525+t.val,by omega⟩)
    let v := fun i : Fin 8 => (translatedEntry t i.val : R)
    let normal := fun i : Fin 8 => (targetNormal t i : R)
    let stored := fun j : Fin 661 => (selectedFrame w (Frames.initialRefs j.val)).symm
      (chartedPhaseRead n owner x g z j.val)
    ∀ s : Swap.Shear.State (Fin 8) R,
      let delta := ((4:R)⁻¹*(normal ⬝ᵥ (s.1-s.2))) • (V *ᵥ v)
      chartedPhaseRead n owner y g z (111+t.val) (s.1-delta,s.2+delta) =
        (stored ⟨111+t.val,by omega⟩ + stored ⟨t.val,by omega⟩) (M8.Exchange.exchange (1-P) s) := by
  intro R P V v normal stored s delta
  have encoded := chartedPhase_encode n owner x g z
  have target := (portTransfer_endpoint w t stored s).2
  rw [encoded,← run] at target
  exact target

open IntegerMultBounds.Swap.Modular M8.RevMachine in
/-- The inverse port pass on a finished target tape exposes the decoded
sum at the logical target address, for arbitrary owner inputs and labels. -/
theorem chartedTarget_owner [M8.Machine.Net] (t : Fin 111) :
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w B K,
      0 < w → 0 < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner V),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*V + LeafCore.coreCost V w + 6 ∧
        ∀ n (owner : Fin 661 ↪ Fin 142081) x y g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B),
          chartedPhaseRead n owner y g z =
            runSelected (selectedFrame w) (selectedWord w) (chartedPhaseRead n owner x g z) →
          let dst : Fin 661 := ⟨111+t.val,by omega⟩
          let src : Fin 661 := ⟨t.val,by omega⟩
          let stored := fun j : Fin 661 => (selectedFrame w (Frames.initialRefs j.val)).symm
            (chartedPhaseRead n owner x g z j.val)
          ∀ s, stage.transform (y (owner dst)) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
            (labelSpectator (g*registerChart w n dst.val) z)) =
            (stored dst + stored src) (M8.Exchange.exchange (1-P) s) := by
  obtain ⟨c,machine,correct⟩ := portCorrection_owner t true true
  refine ⟨c,machine,?_⟩
  intro w B K hw hW W V P
  obtain ⟨stage,fixed,cost,read⟩ := correct w W hw hW
  refine ⟨stage,fixed,cost,?_⟩
  intro n owner x y g z run dst src stored s
  apply (read (y (owner dst)) s (labelSpectator (g*registerChart w n dst.val) z)).trans
  have endpoint := chartedTarget_read g z run t s
  have move := ((portFrame_transfers w t).2.2 s).2
  have raw (a : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
      chartedPhaseRead n owner y g z (111+t.val) a = y (owner dst)
        (FlatCoordinateLayout.index (AffineFieldCoordinates.embed a) (labelSpectator (g*registerChart w n dst.val) z)) := by
    simp [chartedPhaseRead,phaseRead,Copy.extendStored,show 111+t.val < 661 by omega,dst]
  dsimp only at endpoint
  rw [raw] at endpoint
  simpa only [ite_true,move] using endpoint

private theorem executePorts {k V : ℕ} {α : Type*} (slot : α ↪ Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V))
    (ts : List α) (unique : ts.Nodup) (data : Fin (k+1) → Fin V → ZMod 2) :
    let out := SharedBankStage.execute (ts.map fun t => placePort (slot t) (port t)) data
    (∀ t ∈ ts, out (slot t) = (port t).transform (data (slot t))) ∧
      ∀ i, (∀ t ∈ ts, slot t ≠ i) → out i = data i := by
  induction ts generalizing data with
  | nil => exact ⟨by simp,fun _ _ => rfl⟩
  | cons t ts ih =>
    let next := Function.update data (slot t) ((port t).transform (data (slot t)))
    obtain ⟨hits,off⟩ := ih (List.nodup_cons.mp unique).2 next
    change (∀ a ∈ t::ts, SharedBankStage.execute _ next (slot a) = _) ∧ _
    constructor
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | inside
      · rw [off]
        · exact Function.update_self ..
        · intro b hb eq
          exact (List.nodup_cons.mp unique).1 (slot.injective eq ▸ hb)
      · rw [hits a inside]
        have ne : a ≠ t := fun e => (List.nodup_cons.mp unique).1 (e ▸ inside)
        rw [show next (slot a) = data (slot a) from Function.update_of_ne (slot.injective.ne ne) ..]
    · intro i away
      exact (off i (fun b hb => away b (List.mem_cons_of_mem _ hb))).trans
        (Function.update_of_ne (away t List.mem_cons_self).symm ..)

theorem compilePortsSized {k V : ℕ} {α : Type*} (slot : α ↪ Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (ts : List α) (unique : ts.Nodup) :
    ∃ post : SharedBankStage.Stage _ (k+1) prime (phaseOwners (N := V)),
      post.tapes = k+1 + (ts.map fun t => k+1+((port t).tapes+k)).sum ∧
      post.states = (ts.map fun t => (port t).states).sum + 1 ∧
      post.cost = (ts.map fun t => (port t).cost).sum + ts.length ∧
      (∀ data t, t ∈ ts → post.transform data (slot t) = (port t).transform (data (slot t))) ∧
      ∀ data i, (∀ t ∈ ts, slot t ≠ i) → post.transform data i = data i := by
  let stages := ts.map fun t => placePort (slot t) (port t)
  refine ⟨SharedBankStage.compile _ (Nat.zero_lt_succ _) stages,?_,?_,?_,?_,?_⟩
  · clear unique
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      change (k+1+((port t).tapes+k)) + (SharedBankStage.compile _ _ (ts.map _)).tapes = _
      simp only [List.map_cons,List.sum_cons]
      dsimp only [stages] at ih
      rw [ih]; omega
  · clear unique
    induction ts with
    | nil => rfl
    | cons t ts ih =>
      change (port t).states + (SharedBankStage.compile _ _ (ts.map _)).states = _
      dsimp only [stages] at ih
      rw [ih]; simp [Nat.add_assoc]
  · simp only [SharedBankStage.compile_cost,stages,List.map_map,List.length_map]
    rfl
  · intro data t ht
    rw [SharedBankStage.compile_transform]
    exact (executePorts slot port ts unique data).1 t ht
  · intro data i away
    rw [SharedBankStage.compile_transform]
    exact (executePorts slot port ts unique data).2 i away

theorem compilePorts {k V : ℕ} {α : Type*} (slot : α ↪ Fin (k+1))
    (port : α → SharedBankStage.Stage _ 1 prime (@portOwner V)) (ts : List α) (unique : ts.Nodup) :
    ∃ post : SharedBankStage.Stage _ (k+1) prime (phaseOwners (N := V)),
      post.cost = (ts.map fun t => (port t).cost).sum + ts.length ∧
      (∀ data t, t ∈ ts → post.transform data (slot t) = (port t).transform (data (slot t))) ∧
      ∀ data i, (∀ t ∈ ts, slot t ≠ i) → post.transform data i = data i := by
  obtain ⟨s,_,_,cost,hits,off⟩ := compilePortsSized slot port ts unique
  exact ⟨s,cost,hits,off⟩

open IntegerMultBounds.Swap.Modular M8.RevMachine in
/-- Append all 111 target corrections to a charted invocation. Each
target is visited once, and every other permanent tape retains the
invocation's output. The bill includes every pass and program join. -/
theorem chartedTargets_stage [M8.Machine.Net] :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      ∀ n (owner : Fin 661 ↪ Fin 142081) (mid : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))),
      (∀ x g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B), chartedPhaseRead n owner (mid.transform x) g z =
        runSelected (selectedFrame w) (selectedWord w) (chartedPhaseRead n owner x g z)) →
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost = mid.cost + C*V + 111*(LeafCore.coreCost V w + 7) + 1 ∧
        (∀ x g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) s,
          let dst : Fin 661 := ⟨111+t.val,by omega⟩
          let src : Fin 661 := ⟨t.val,by omega⟩
          let stored := fun j : Fin 661 => (selectedFrame w (Frames.initialRefs j.val)).symm
            (chartedPhaseRead n owner x g z j.val)
          let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
          stage.transform x (owner dst) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
            (labelSpectator (g*registerChart w n dst.val) z)) =
            (stored dst + stored src) (M8.Exchange.exchange (1-P) s)) ∧
        ∀ x i, (∀ t : Fin 111, owner ⟨111+t.val,by omega⟩ ≠ i) → stage.transform x i = mid.transform x i := by
  choose c machine run using chartedTarget_owner
  let ts := List.finRange 111
  refine ⟨(ts.map c).sum,?_⟩
  intro w B K hw hW W V n owner mid word
  choose port _ price read using fun t => run t w B K hw hW
  let slot : Fin 111 ↪ Fin 142081 := ⟨fun t => owner ⟨111+t.val,by omega⟩,by
    intro a b eq
    have val := congrArg Fin.val (owner.injective eq)
    exact Fin.ext (Nat.add_left_cancel val)⟩
  obtain ⟨post,cost,hits,off⟩ := compilePorts slot port ts (List.nodup_finRange _)
  refine ⟨SharedBankStage.compose mid post,?_,?_,?_⟩
  · change mid.cost + post.cost + 1 = _
    rw [cost]
    simp only [price,List.sum_map_add,List.sum_map_mul_right,List.map_const',List.sum_replicate,nsmul_eq_mul,
      ts,List.length_finRange]
    ring
  · intro x g z t s dst src stored P
    exact (congrFun (hits (mid.transform x) t (List.mem_finRange t)) _).trans
      (read t n owner x (mid.transform x) g z (word x g z) s)
  · intro x i away
    exact off (mid.transform x) i (fun t _ => away t)

private theorem chartedOwner_read {n : Fin 9} {owner : Fin 661 ↪ Fin 142081} {w B K : ℕ}
    (x) (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B)
    (j : Fin 661) s :
    chartedPhaseRead n owner x g z j.val s = x (owner j) (FlatCoordinateLayout.index
      (AffineFieldCoordinates.embed s) (labelSpectator (g*registerChart w n j.val) z)) := by
  simp [chartedPhaseRead,phaseRead,Copy.extendStored,j.isLt]

open IntegerMultBounds.Swap.Modular M8.RevMachine in
/-- Prepare the 111 source tapes so decoding their physical initial frames
reads exactly the logical port exchange on the caller's original bank. -/
theorem chartedSources_stage [M8.Machine.Net] :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      ∀ (owner : Fin 661 ↪ Fin 142081),
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost = C*V + 111*(LeafCore.coreCost V w+7) ∧
        (∀ n x g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111),
          let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
          (selectedFrame w (Frames.initialRefs t.val)).symm
            (chartedPhaseRead n owner (stage.transform x) g z t.val) =
              fun s => chartedPhaseRead n owner x g z t.val (M8.Exchange.exchange P s)) ∧
        ∀ x i, (∀ t : Fin 111, owner ⟨t.val,by omega⟩ ≠ i) → stage.transform x i = x i := by
  choose c machine run using fun t => portCorrection_owner t false true
  let ts := List.finRange 111
  refine ⟨(ts.map c).sum,?_⟩
  intro w B K hw hW W V owner
  choose port _ price read using fun t => run t w W hw hW
  let src (t : Fin 111) : Fin 661 := ⟨t.val,by omega⟩
  let slot : Fin 111 ↪ Fin 142081 := ⟨fun t => owner (src t),by intro a b h; exact Fin.ext (congrArg (Fin.val : Fin 661 → ℕ) (owner.injective h))⟩
  obtain ⟨stage,cost,hits,off⟩ := compilePorts slot port ts (List.nodup_finRange _)
  refine ⟨stage,?_,?_,fun x i away => off x i (fun t _ => away t)⟩
  · rw [cost]
    simp only [price,ite_true,List.sum_map_add,List.sum_map_mul_right,List.map_const',List.sum_replicate,
      nsmul_eq_mul,ts,List.length_finRange]
    ring
  · intro n x g z t P
    apply (selectedFrame w (Frames.initialRefs t.val)).injective
    rw [LinearEquiv.apply_symm_apply]
    funext s
    rw [(portFrame_absorption w t).2.2.2.2.1]
    rw [chartedOwner_read _ _ _ (src t),chartedOwner_read _ _ _ (src t)]
    exact (congrFun (hits x t (List.mem_finRange t)) _).trans (read t (x (slot t)) s _)

open Matrix in
private theorem port_complements_swap (w : ℕ) (t : Fin 111) (s : IntegerMultBounds.Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
    M8.Exchange.exchange P (M8.Exchange.exchange (1-P) s) = s.swap := by
  intro P
  obtain ⟨up,pu,_⟩ := portFrame_absorption w t
  have idem : P*P=P := by
    calc P*P = P*(_*P) := congrArg (P*·) up.symm
         _ = P := by rw [← Matrix.mul_assoc,pu,up]
  have comp : M8.Exchange.exchange (1-P) s = M8.Exchange.exchange P s.swap := by
    simp [M8.Exchange.exchange,add_comm]
  rw [comp,M8.Global.exchange_involutive idem]

open Matrix in
theorem emptyFrame_decode (w : ℕ) (f : AddressStream (ZMod (prime^w))) :
    (selectedFrame w 0).symm f = f := by
  apply (selectedFrame w 0).injective
  rw [LinearEquiv.apply_symm_apply]
  have mask := (selectedProjector_mask w (0 : Fin 636)).1
  have dim : Geometry.Dimensions.value 0 = 0 := by decide
  change _ * prefixMask _ (Geometry.Dimensions.value 0) = _ at mask
  rw [dim,show prefixMask (ZMod (prime^w)) 0 = 0 by simp [prefixMask],mul_zero] at mask
  funext s
  have atZero := selectedFrame_rational w (0 : Fin 636) f s
  rw [← mask] at atZero
  simpa [M8.Exchange.exchange] using atZero.symm

open Matrix in
theorem fullFrame_read (w : ℕ) (f : AddressStream (ZMod (prime^w))) (s) :
    selectedFrame w 1 f s = f s.swap := by
  have mask := (selectedProjector_mask w (1 : Fin 636)).2
  change prefixMask _ (Geometry.Dimensions.value 1) * _ = prefixMask _ (Geometry.Dimensions.value 1) at mask
  have full : prefixMask (ZMod (prime^w)) 8 = 1 := by
    unfold prefixMask
    simp only [Fin.is_lt,ite_true]
    rfl
  rw [Nine.full_dimension,full,one_mul] at mask
  have read := selectedFrame_rational w (1 : Fin 636) f s
  rw [mask] at read
  cases s
  simpa [M8.Exchange.exchange] using read

private theorem chartedWord_retained {w B K : ℕ} {n : Fin 9} {owner : Fin 661 ↪ Fin 142081}
    {x y} {g : Cover.LabelPadding.Label 64 w} {z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B}
    (run : chartedPhaseRead n owner y g z = runSelected (selectedFrame w) (selectedWord w) (chartedPhaseRead n owner x g z))
    (i : Fin 661) (nonTarget : ¬ (111 ≤ i.val ∧ i.val < 222)) :
    chartedPhaseRead n owner y g z i.val = selectedFrame w (Frames.finalRefs i.val)
      ((selectedFrame w (Frames.initialRefs i.val)).symm (chartedPhaseRead n owner x g z i.val)) := by
  let stored := fun j : Fin 661 => (selectedFrame w (Frames.initialRefs j.val)).symm (chartedPhaseRead n owner x g z j.val)
  have encoded := chartedPhase_encode n owner x g z
  have word := ((runSelected_endpoint w).2 stored).trans (Framed.execute_endpoint (selectedFrame w) stored).symm
  have row := (congrFun word i.val).trans (Framed.execute_dirty (selectedFrame w) stored i)
  rw [dite_eq_right nonTarget,encoded,← run] at row
  exact row

open Cover IntegerMultBounds.Swap.Modular in
/-- The physical read contract of a decoded invocation on its caller's tapes. -/
def DecodedInvocationEffect (n : Fin 9) (r : Fin 32) (d : Fin 5) (w B K : ℕ)
    (x y : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
  (∀ g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) s,
    let dst : Fin 661 := ⟨111+t.val,by omega⟩
    let src : Fin 661 := ⟨t.val,by omega⟩
    let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
    y (owner dst) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s)
      (labelSpectator (g*registerChart w n dst.val) z)) =
      chartedPhaseRead n owner x g z dst.val (M8.Exchange.exchange (1-P) s) +
      chartedPhaseRead n owner x g z src.val s.swap) ∧
  (∀ g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) s,
    let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
    chartedPhaseRead n owner (y) g z t.val s =
      chartedPhaseRead n owner x g z t.val (M8.Exchange.exchange P s.swap)) ∧
  (∀ g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (h : Fin 439) s,
    chartedPhaseRead n owner (y) g z (222+h.val) s =
      chartedPhaseRead n owner x g z (222+h.val) s.swap) ∧
  ∀ i, i ≠ Fin.last 142080 → (∀ j, owner j ≠ i) → y i = x i

open Cover IntegerMultBounds.Swap.Modular in
/-- A target and its matching source share one chart, so both input streams
are read at the unchanged physical label. -/
theorem DecodedInvocationEffect.target {n r d w B K x y}
    (run : DecodedInvocationEffect n r d w B K x y)
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
    (t : Fin 111) s :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let dst : Fin 661 := ⟨111+t.val,by omega⟩
    let src : Fin 661 := ⟨t.val,by omega⟩
    let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
    y (owner dst) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (labelSpectator g z)) =
      x (owner dst) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed (M8.Exchange.exchange (1-P) s)) (labelSpectator g z)) +
      x (owner src) (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s.swap) (labelSpectator g z)) := by
  intro owner dst src P
  have charts : registerChart w n src.val = registerChart w n dst.val := by
    unfold registerChart
    rw [(chart_port n t).1,(chart_port n t).2]
  have eq := run.1 (g*(registerChart w n dst.val).transpose) z t s
  dsimp only at eq
  change _ = chartedPhaseRead n owner x _ z dst.val _ + chartedPhaseRead n owner x _ z src.val _ at eq
  rw [chartedOwner_read (j := dst),chartedOwner_read (j := src),charts] at eq
  have cancel : g*(registerChart w n dst.val).transpose*registerChart w n dst.val = g := by
    rw [Matrix.mul_assoc,registerChart_inverse,Matrix.mul_one]
  rw [cancel] at eq
  exact eq

/-- Read an eight-axis stream on the parent address, using its exterior digits
and trailing position to select the spectator record. -/
noncomputable def windowRead {Q W : ℕ} [NeZero Q]
    (read : Fin (Q^112*W) → AddressStream (ZMod Q))
    (s : Swap.Shear.State Nine.Axis (ZMod Q)) (j : Fin W) :=
  let a := copyAddress (chartAddress (s,j))
  read a.2 a.1

private theorem windowRead_exchange {Q W : ℕ} [NeZero Q] (n : Fin 9)
    (U V : Matrix (Fin 8) (Fin 8) (ZMod Q)) (read : Fin (Q^112*W) → AddressStream (ZMod Q))
    (s : Swap.Shear.State Nine.Axis (ZMod Q)) (j : Fin W) :
    let L := Matrix.diagonal fun i : Nine.Exterior => if i.1.val < n.val then (1 : ZMod Q) else 0
    let frame := fun P => M8.Exchange.exchange (Matrix.fromBlocks P 0 0 L)
    windowRead read (frame V (frame U s)) j =
      windowRead (fun k a => read k (M8.Exchange.exchange V (M8.Exchange.exchange U a))) s j := by
  intro L frame
  unfold windowRead
  rw [← chartAddress_exchange n U V s j,Equiv.apply_symm_apply]

open Matrix IntegerMultBounds.Swap.Modular in
private theorem portExchange_inverse_translation (w : ℕ) (t : Fin 111)
    (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
    let physical := M8.Exchange.transform D⁻¹ D⁻¹
    let L := reduce (prime^w) (Nine.port t.val).lineProj
    let P := translatedPortProjector (ZMod (prime^w)) (4:ZMod (prime^w))⁻¹ t
    physical (M8.Exchange.exchange L s) = M8.Exchange.exchange P (physical s) ∧
      physical (M8.Exchange.exchange (1-L) s) = M8.Exchange.exchange (1-P) (physical s) := by
  intro D physical L P
  have unit := (isUnit_iff_isUnit_det D).mp (translatedPort_modular w t).1
  have cancel (a : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
      M8.Exchange.transform D D (physical a) = a := by
    simp [physical,M8.Exchange.transform,mulVec_mulVec,mul_nonsing_inv D unit]
  have undo (a : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
      physical (M8.Exchange.transform D D a) = a := by
    simp [physical,M8.Exchange.transform,mulVec_mulVec,nonsing_inv_mul D unit]
  obtain ⟨src,dst⟩ := portExchange_original w t (physical s)
  change M8.Exchange.transform D D _ = M8.Exchange.exchange L (M8.Exchange.transform D D (physical s)) at src
  change M8.Exchange.transform D D _ = M8.Exchange.exchange (1-L) (M8.Exchange.transform D D (physical s)) at dst
  rw [cancel] at src dst
  exact ⟨(congrArg physical src.symm).trans (undo _),(congrArg physical dst.symm).trans (undo _)⟩

open IntegerMultBounds.Swap.Modular in
/-- Lift the two corrected port equations to the full modular window.
The exterior prefix cancels between consecutive exchanges. -/
theorem activePort_window {w W : ℕ} (n : Fin 9) (t : Fin 111)
    (src dst srcOut dstOut : Fin ((prime^w)^112*W) → AddressStream (ZMod (prime^w)))
    (step : ∀ k a, let P := translatedPortProjector (ZMod (prime^w)) (4 : ZMod (prime^w))⁻¹ t
      srcOut k a = src k (M8.Exchange.exchange P a.swap) ∧
      dstOut k a = dst k (M8.Exchange.exchange (1-P) a) + src k a.swap)
    (s : Swap.Shear.State Nine.Axis (ZMod (prime^w))) (j : Fin W) :
    let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
    let physical := M8.Exchange.transform D⁻¹ D⁻¹
    let read := fun f => windowRead (fun k a => f k (physical a))
    let L := Matrix.diagonal fun i : Nine.Exterior => if i.1.val < n.val then (1 : ZMod (prime^w)) else 0
    let frame := fun (P : Matrix (Fin 8) (Fin 8) (ZMod (prime^w))) =>
      M8.Exchange.exchange (Matrix.fromBlocks P 0 0 L)
    let P := reduce (prime^w) (Nine.port t.val).lineProj
    read srcOut s j = read src (frame P (frame 1 s)) j ∧
      read dstOut s j = read dst (frame (1-P) (frame 0 s)) j + read src (frame 1 (frame 0 s)) j := by
  intro D physical read L frame P
  let a := copyAddress (chartAddress (s,j))
  have zero (v : Swap.Shear.State (Fin 8) (ZMod (prime^w))) : M8.Exchange.exchange 0 v = v := by simp [M8.Exchange.exchange]
  have one (v : Swap.Shear.State (Fin 8) (ZMod (prime^w))) : M8.Exchange.exchange 1 v = v.swap := by
    simp [M8.Exchange.exchange,Prod.swap]
  simp only [read,frame,L,windowRead_exchange,zero,one,windowRead]
  obtain ⟨source,target⟩ := step a.2 (physical a.1)
  exact ⟨source.trans (congrArg (src a.2) (portExchange_inverse_translation w t a.1.swap).1.symm),
    target.trans (congrArg (fun v => dst a.2 v + src a.2 (physical a.1.swap))
      (portExchange_inverse_translation w t a.1).2.symm)⟩

open IntegerMultBounds.Swap.Modular in
/-- The decoded physical invocation acts on both full parent address halves.
The shared exterior prefix cancels in each pair of stage frames. -/
theorem DecodedInvocationEffect.window {n r d w B W x y}
    (run : DecodedInvocationEffect n r d w B ((prime^w)^112*W) x y)
    (g : Cover.LabelPadding.Label 64 w)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B ((prime^w)^112*W)) B)
    (s : Swap.Shear.State Nine.Axis (ZMod (prime^w))) (j : Fin W) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let cells := fun k => { z with after := k }
    let D := undoTranslation.map (Int.cast : ℤ → ZMod (prime^w))
    let physical := M8.Exchange.transform D⁻¹ D⁻¹
    let read := fun bank i => windowRead (fun k b => chartedPhaseRead n owner bank g (cells k) i (physical b))
    let L := Matrix.diagonal fun i : Nine.Exterior => if i.1.val < n.val then (1 : ZMod (prime^w)) else 0
    let frame := fun (P : Matrix (Fin 8) (Fin 8) (ZMod (prime^w))) =>
      M8.Exchange.exchange (Matrix.fromBlocks P 0 0 L)
    (∀ t : Fin 111, let P := reduce (prime^w) (Nine.port t.val).lineProj
      read y (111+t.val) s j = read x (111+t.val) (frame (1-P) (frame 0 s)) j +
        read x t.val (frame 1 (frame 0 s)) j ∧
      read y t.val s j = read x t.val (frame P (frame 1 s)) j) ∧
    ∀ h : Fin 439, read y (222+h.val) s j = read x (222+h.val) (frame 1 (frame 0 s)) j := by
  intro owner cells D physical read L frame
  let a := copyAddress (chartAddress (s,j))
  have zero (b : Swap.Shear.State (Fin 8) (ZMod (prime^w))) : M8.Exchange.exchange 0 b = b := by
    simp [M8.Exchange.exchange]
  have one (b : Swap.Shear.State (Fin 8) (ZMod (prime^w))) : M8.Exchange.exchange 1 b = b.swap := by
    simp [M8.Exchange.exchange,Prod.swap]
  constructor
  · intro t P
    let dst : Fin 661 := ⟨111+t.val,by omega⟩
    let src : Fin 661 := ⟨t.val,by omega⟩
    let row := fun bank i k => chartedPhaseRead n owner bank g (cells k) i
    have moved := activePort_window n t (row x src.val) (row x dst.val) (row y src.val) (row y dst.val) (by
      intro k v
      refine ⟨run.2.1 g (cells k) t v,?_⟩
      rw [show row y dst.val k v = _ from chartedOwner_read (n := n) (owner := owner) y g (cells k) dst v]
      exact run.1 g (cells k) t v) s j
    exact moved.symm
  · intro h
    simp only [read,frame,L,windowRead_exchange,zero,one,windowRead]
    exact run.2.2.1 g (cells a.2) h (physical a.1)

/-- Each output row of the selected word depends only on itself and,
for a target, its paired source. -/
private theorem selectedRow (w : ℕ) (rows : Fin 661 → AddressStream (ZMod (prime^w))) (i : Fin 661) :
    let stored := fun j : Fin 661 => (selectedFrame w (Frames.initialRefs j.val)).symm (rows j)
    runSelected (selectedFrame w) (selectedWord w) (Copy.extendStored rows) i.val =
      selectedFrame w (Frames.finalRefs i.val)
        (if h : 111 ≤ i.val ∧ i.val < 222 then stored i + stored ⟨i.val-111,by omega⟩ else stored i) := by
  intro stored
  have encoded : FramedCircuit.encode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (Copy.extendStored stored) = Copy.extendStored rows := by
    funext j
    by_cases h : j < 661 <;> simp [FramedCircuit.encode,Frames.snapshot,Copy.extendStored,stored,h]
  have word := ((runSelected_endpoint w).2 stored).trans (Framed.execute_endpoint (selectedFrame w) stored).symm
  have row := (congrFun word i.val).trans (Framed.execute_dirty (selectedFrame w) stored i)
  rwa [encoded] at row

private theorem common_charted_read {w B K n} {owner : Fin 661 ↪ Fin 142081} {x y}
    (common : ∀ g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B),
      phaseRead owner y (labelSpectator g z) =
        runSelected (selectedFrame w) (selectedWord w) (phaseRead owner x (labelSpectator g z)))
    (g : Cover.LabelPadding.Label 64 w) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B)
    (i : Fin 661) :
    chartedPhaseRead n owner y g z i.val =
      runSelected (selectedFrame w) (selectedWord w) (chartedPhaseRead n owner x g z) i.val := by
  let h := g*registerChart w n i.val
  let rows : Fin 661 → AddressStream (ZMod (prime^w)) := fun j s => x (owner j) (FlatCoordinateLayout.index
    (AffineFieldCoordinates.embed s) (labelSpectator h z))
  let charted := fun j : Fin 661 => phaseRead owner x (labelSpectator (g*registerChart w n j.val) z) j.val
  have read := congrFun (common h z) i.val
  change _ = runSelected _ _ (Copy.extendStored rows) i.val at read
  change _ = runSelected _ _ (Copy.extendStored charted) i.val
  rw [selectedRow] at read ⊢
  have same : charted i = rows i := by simp [charted,rows,h,phaseRead,Copy.extendStored]
  simp only [chartedPhaseRead,Copy.extendStored,dite_eq_left i.isLt]
  rw [read]
  dsimp only
  rw [same]
  split
  · rename_i target
    let t : Fin 111 := ⟨i.val-111,by omega⟩
    have idx : i.val = 111+t.val := by dsimp [t]; omega
    have charts : registerChart w n t.val = registerChart w n i.val := by
      unfold registerChart
      rw [idx,(chart_port n t).1,(chart_port n t).2]
    have src : charted ⟨t.val,by omega⟩ = rows ⟨t.val,by omega⟩ := by
      simp [charted,rows,h,phaseRead,Copy.extendStored,charts]
    rw [src]
  · rfl

open Cover IntegerMultBounds.Swap.Modular M8.RevMachine in
/-- The charged PR589 invocation on the caller’s charted tapes. Sources
pass through their logical line frames, targets receive their transposed
sources, and all helper streams undergo the full address interchange. -/
theorem decodedInvocation_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
      let bill := fun (gates : List RawGate) (current : ℕ → ℕ) =>
        let code := FramedCircuit.compile (fun i => selectedFrame w (current i))
          (gates.map (Frames.framedGate (selectedFrame w)))
        (code.map (scalarWork V)).sum + ((Frames.edges gates current).map (phaseEdgeBudget owner w W)).sum + code.length
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ bill (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) +
          bill (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) +
          C*V + 9*engine.time (copyChild w W) hs + 222*(LeafCore.coreCost V w+7) + 13 ∧
        ∀ x, DecodedInvocationEffect n r d w B K x (stage.transform x) := by
  obtain ⟨C,word⟩ := commonInvocation_stage n r d engine
  obtain ⟨D,finish⟩ := chartedTargets_stage
  obtain ⟨E,prepare⟩ := chartedSources_stage
  refine ⟨E+C+D,?_⟩
  intro w B K hw hB hK W V owner bill hs
  obtain ⟨mid,cost,common,keep⟩ := word w B K hw hB hK
  have read (x g z) : chartedPhaseRead n owner (mid.transform x) g z =
      runSelected (selectedFrame w) (selectedWord w) (chartedPhaseRead n owner x g z) := by
    funext j
    by_cases inside : j < 661
    · exact common_charted_read (common x) g z ⟨j,inside⟩
    · let stored := fun i : Fin 661 => (selectedFrame w (Frames.initialRefs i.val)).symm
            (chartedPhaseRead n owner x g z i.val)
      have word := (runSelected_endpoint w).2 stored
      rw [chartedPhase_encode n owner x g z] at word
      rw [word]
      simp [FramedCircuit.encode,Framed.moduleRun_high program Framed.program_target_lt _ j (by omega),
        chartedPhaseRead,Copy.extendStored,inside]
  have hW : 0 < W := Nat.mul_pos (Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _)) hK
  obtain ⟨stage,price,target,off⟩ := finish w B K hw hW n owner mid read
  obtain ⟨pre,preCost,source,preserve⟩ := prepare w B K hw hW owner
  have postRead (x g z) (i : Fin 661) (outside : ¬ (111 ≤ i.val ∧ i.val < 222)) :
      chartedPhaseRead n owner (stage.transform x) g z i.val =
        chartedPhaseRead n owner (mid.transform x) g z i.val := by
    funext s
    rw [chartedOwner_read _ _ _ i,chartedOwner_read _ _ _ i]
    exact congrFun (off x (owner i) (fun t h => by
      have eq := congrArg Fin.val (owner.injective h)
      change 111+t.val = i.val at eq
      omega)) _
  refine ⟨SharedBankStage.compose pre stage,?_,?_⟩
  · change pre.cost + stage.cost + 1 ≤ _
    change mid.cost ≤ bill (sectionD++sectionA) (Frames.snapshot Frames.initialRefs) +
      (C*V + 9*engine.time (copyChild w W) hs + 9) +
      bill (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter) + 2 at cost
    change stage.cost = mid.cost+D*V+111*(LeafCore.coreCost V w+7)+1 at price
    change pre.cost = E*V+111*(LeafCore.coreCost V w+7) at preCost
    rw [preCost,price,Nat.add_mul,Nat.add_mul]
    omega
  intro x
  refine ⟨?_,?_,?_,?_⟩
  · intro g z t s dst src P
    have raw := target (pre.transform x) g z t s
    change stage.transform (pre.transform x) (owner dst) _ = _
    apply raw.trans
    change ((selectedFrame w (Frames.initialRefs dst.val)).symm
      (chartedPhaseRead n owner (pre.transform x) g z dst.val)) (M8.Exchange.exchange (1-P) s) +
      ((selectedFrame w (Frames.initialRefs t.val)).symm
      (chartedPhaseRead n owner (pre.transform x) g z t.val)) (M8.Exchange.exchange (1-P) s) = _
    rw [show Frames.initialRefs dst.val = 0 from (Nine.target_frames t.val t.isLt).1,emptyFrame_decode,source n x g z t]
    have swap : M8.Exchange.exchange P (M8.Exchange.exchange (1-P) s) = s.swap := port_complements_swap w t s
    change _ + chartedPhaseRead n owner x g z src.val (M8.Exchange.exchange P (M8.Exchange.exchange (1-P) s)) = _
    rw [swap]
    apply congrArg (· + chartedPhaseRead n owner x g z src.val s.swap)
    rw [chartedOwner_read _ _ _ dst,chartedOwner_read _ _ _ dst]
    have unchanged := preserve x (owner dst) (fun a h => by
      have eq := congrArg Fin.val (owner.injective h)
      change a.val = 111+t.val at eq
      omega)
    exact congrFun unchanged _
  · intro g z t s P
    let i : Fin 661 := ⟨t.val,by omega⟩
    have nt : ¬ (111 ≤ i.val ∧ i.val < 222) := by change ¬ (111 ≤ t.val ∧ t.val < 222); omega
    change chartedPhaseRead n owner (stage.transform (pre.transform x)) g z i.val s = _
    rw [postRead _ _ _ i nt,chartedWord_retained (read _ g z) i nt,
      show Frames.finalRefs i.val = 1 from (Nine.source_frames t.val t.isLt).2.2,fullFrame_read,source n x g z t]
  · intro g z h s
    let i : Fin 661 := ⟨222+h.val,by omega⟩
    have nt : ¬ (111 ≤ i.val ∧ i.val < 222) := by change ¬ (111 ≤ 222+h.val ∧ 222+h.val < 222); omega
    have refs := Nine.helper_refs h.val h.isLt
    change chartedPhaseRead n owner (stage.transform (pre.transform x)) g z i.val s = _
    rw [postRead _ _ _ i nt,chartedWord_retained (read _ g z) i nt,
      show Frames.finalRefs i.val = 1 from refs.2,fullFrame_read,
      show Frames.initialRefs i.val = 0 from refs.1,emptyFrame_decode]
    rw [chartedOwner_read _ _ _ i,chartedOwner_read _ _ _ i]
    exact congrFun (preserve x (owner i) (fun t eq => by
      have val := congrArg Fin.val (owner.injective eq)
      change t.val = 222+h.val at val
      omega)) _
  · intro i hi away
    exact (off (pre.transform x) i (fun _ => away _)).trans
      ((keep (pre.transform x) i hi away).trans (preserve x i (fun _ => away _)))

open M8.Machine in
/-- The routed scatter runs on exactly the flat owner bank consumed by the
phase programs. Reindexing its proof across the volume equality costs no steps. -/
theorem invocationScatter_stage [Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      let view := fun (data : Fin 142081 → Fin V → ZMod 2) k i => data k (Fin.cast (copyLabel_volume w B K) i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + 2*(63*9+252*527)*M8.RevMachine.LeafCore.coreCost V (w*64) +
          9*engine.time (copyChild w W) hs + 9 ∧
        ∀ data, CopyScheduleEffect n r d w B K Copy.lifecycles (view data) (view (stage.transform data)) := by
  obtain ⟨C,run⟩ := routedCopy_schedule n r d engine
  refine ⟨C,?_⟩
  intro w B K hw hB hK W V hs view
  obtain ⟨stage,acts,bill⟩ := run w B K hw hB hK
  apply flatCopyStage (copyLabel_volume w B K) _ _ stage acts
  convert bill using 1
  rw [copyLabel_volume]

noncomputable def labelPhase (w : ℕ) (gates : List RawGate) (current : ℕ → ℕ)
    (bank : ℕ → AddressStream (ZMod (prime^w))) :=
  let frame := selectedFrame w
  FramedCircuit.encode (fun i => frame (Frames.run gates current i))
    (FramedCircuit.moduleRun (gates.map RawGate.toCircuit) (FramedCircuit.decode (fun i => frame (current i)) bank))

/-- Scalar gates and instruction joins cost a fixed multiple of the volume.
The coefficient depends only on the literal gates, including repeated inputs. -/
theorem compiled_overhead {w : ℕ} (V : ℕ) (positive : 0 < V)
    (gs : List RawGate) (frame current : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w)))) :
    let code := FramedCircuit.compile current (gs.map (Frames.framedGate frame))
    (code.map (scalarWork V)).sum + code.length ≤
      (gs.map (fun g => 77*g.sources.length+2)).sum*V := by
  intro code
  have edges (wires : List ℕ) (a b : ℕ → FramedCircuit.Frame (ZMod 2) (AddressStream (ZMod (prime^w)))) :
      let es := FramedCircuit.edges a b wires
      (es.map (scalarWork V)).sum = 0 ∧ es.length = wires.length := by
    induction wires generalizing a with
    | nil => exact ⟨rfl,rfl⟩
    | cons i rest ih =>
      simp only [FramedCircuit.edges,List.map_cons,List.sum_cons,scalarWork,List.length_cons,Nat.zero_add]
      exact ⟨(ih _).1,congrArg Nat.succ (ih _).2⟩
  induction gs generalizing current with
  | nil => simp [code,FramedCircuit.compile]
  | cons g gs ih =>
    let v := Frames.framedGate frame g
    have tail := ih (FramedCircuit.afterGate current v)
    have e := edges (FramedCircuit.touched g.toCircuit) current (fun _ => frame g.frame)
    dsimp only at e tail
    simp only [code,List.map_cons,FramedCircuit.compile]
    simp only [FramedCircuit.compileGate,Frames.framedGate,List.map_append,List.sum_append,
      List.length_append,List.map_cons,List.sum_cons,List.length_cons,List.length_nil,List.map_nil,List.sum_nil,
      scalarWork,e.1,e.2]
    have terms : g.toCircuit.terms.length = g.sources.length := List.length_map _
    simp only [Frames.touched_toCircuit,Frames.touched,List.length_cons,terms,Nat.add_mul]
    have h := Nat.mul_le_mul_right (g.sources.length+2) (Nat.succ_le_of_lt positive)
    simp only [Nat.one_mul,Nat.mul_add] at h
    simp only [v,Frames.framedGate] at tail
    nlinarith only [tail,h,positive]

open M8.Machine in
theorem phaseEdgeBudget_sum [Net] {k : ℕ} (owner : Fin 661 ↪ Fin k) (w W : ℕ) (price : ℕ → ℕ)
    (positive : 0 < (prime^w)^16*W)
    (bound : ∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
      phaseChildCost w W p ≤ price (Geometry.moveRank p.1 p.2)) :
    let edges := Geometry.Moves.phaseEdges
    let paid := edges.filter (fun p => Geometry.moveRank p.1 p.2 != 0)
    (edges.map (phaseEdgeBudget owner w W)).sum ≤
      (paid.map (fun p => 1303+edgeBasis owner p)).sum*((prime^w)^16*W) +
      ((Geometry.Moves.phaseValues.filter (· != 0)).map price).sum := by
  intro edges paid
  have strip (ps : List (ℕ × ℕ)) :
      (ps.map (phaseEdgeBudget owner w W)).sum =
      ((ps.filter (fun p => Geometry.moveRank p.1 p.2 != 0)).map
        (fun p => phaseWork (edgeBasis owner p) ((prime^w)^16*W) (phaseChildCost w W p))).sum := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      by_cases zero : Geometry.moveRank p.1 p.2 = 0 <;> simp [phaseEdgeBudget,phaseChildCost,zero,ih]
  rw [strip]
  exact phaseWork_sum _ _ _ positive bound

open M8.Machine in
/-- One physical invocation sequences D+A, the nine routed COPY windows,
and B+C. The intermediate states carry both the modular and cover-label reads. -/
theorem invocation_stage [Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C D : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
      let gates := fun done : Bool => if done then sectionB ++ sectionC else sectionD ++ sectionA
      let current := fun done : Bool => if done then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
      let frame := selectedFrame w
      let instructions := fun done => FramedCircuit.compile (fun i => frame (current done i)) ((gates done).map (Frames.framedGate frame))
      let edges := fun done => Frames.edges (gates done) (current done)
      let phaseCost := fun done => ((instructions done).map (scalarWork V)).sum +
        ((edges done).map (phaseEdgeBudget owner w W)).sum + (instructions done).length
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      let scatterCost := C*V + 2*(63*9+252*527)*M8.RevMachine.LeafCore.coreCost V (w*64) +
        9*engine.time (copyChild w W) hs + 9
      let view := fun (data : Fin 142081 → Fin V → ZMod 2) k i => data k (Fin.cast (copyLabel_volume w B K) i)
      let phase := fun done (x y : Fin 142081 → Fin V → ZMod 2) =>
        (∀ j, phaseRead owner y j = FramedCircuit.encode (fun i => frame (Frames.run (gates done) (current done) i))
          (FramedCircuit.moduleRun ((gates done).map RawGate.toCircuit)
            (FramedCircuit.decode (fun i => frame (current done i)) (phaseRead owner x j)))) ∧
        ∀ i, (∀ a, owner a ≠ i) → y i = x i
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ phaseCost false + scatterCost + phaseCost true + 2 ∧
        (∀ price : ℕ → ℕ,
          (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
            phaseChildCost w W p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w W) hs ≤ price 7 →
          stage.cost ≤ D*V + 2*(63*9+252*527)*M8.RevMachine.LeafCore.coreCost V (w*64) +
            ((Geometry.Moves.phaseValues.filter (· != 0)).map price).sum + 9*price 7) ∧
        (∀ data (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B),
          phaseRead owner (stage.transform data) (labelSpectator g z) =
            labelPhase w (gates true) (current true) (labelScatter n (fun h =>
              labelPhase w (gates false) (current false) (phaseRead owner data (labelSpectator h z))) g)) ∧
        ∀ data, ∃ before after, phase false data before ∧
          CopyScheduleEffect n r d w B K Copy.lifecycles (view before) (view after) ∧
          phase true after (stage.transform data) := by
  obtain ⟨C,copy⟩ := invocationScatter_stage n r d engine
  let slots : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
  let scalar := fun gs : List RawGate => (gs.map (fun g => 77*g.sources.length+2)).sum
  let paid := Geometry.Moves.phaseEdges.filter (fun p => Geometry.moveRank p.1 p.2 != 0)
  let moves := (paid.map (fun p => 1303+edgeBasis slots p)).sum
  refine ⟨C,scalar (sectionD++sectionA)+scalar (sectionB++sectionC)+moves+C+11,?_⟩
  intro w B K hw hB hK W V owner gates current frame instructions edges phaseCost hs scatterCost view phase
  have hW : 0 < W := Nat.mul_pos (Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _)) hK
  obtain ⟨left,leftCost,leftRead,leftOff⟩ := invocationPhase_stage owner hw hW false
  obtain ⟨right,rightCost,rightRead,rightOff⟩ := invocationPhase_stage owner hw hW true
  obtain ⟨middle,midCost,midRead⟩ := copy w B K hw hB hK
  have checked := Geometry.Moves.phase_checked
  rw [Geometry.Moves.phaseEdges,List.forall_mem_append] at checked
  have first (data j) : phaseRead owner (left.transform data) j =
      labelPhase w (gates false) (current false) (phaseRead owner data j) :=
    (leftRead data j).trans (phaseLogicalRead w _ _ checked.1 _)
  have last (data j) : phaseRead owner (right.transform data) j =
      labelPhase w (gates true) (current true) (phaseRead owner data j) :=
    (rightRead data j).trans (phaseLogicalRead w _ _ checked.2 _)
  refine ⟨SharedBankStage.compose (SharedBankStage.compose left middle) right,?_,?_,?_,?_⟩
  · change left.cost+middle.cost+1+right.cost+1 ≤ _
    change left.cost ≤ phaseCost false at leftCost
    change right.cost ≤ phaseCost true at rightCost
    change middle.cost ≤ scatterCost at midCost
    omega
  · intro price phaseBound copyBound
    have pos : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
    let work := fun done => ((instructions done).map (scalarWork V)).sum + (instructions done).length
    let calls := fun done => ((edges done).map (phaseEdgeBudget owner w W)).sum
    have overhead (done) : work done ≤ scalar (gates done)*V := compiled_overhead V pos _ _ _
    have childBill := phaseEdgeBudget_sum owner w W price pos phaseBound
    change (Geometry.Moves.phaseEdges.map (phaseEdgeBudget owner w W)).sum ≤ moves*V + _ at childBill
    rw [Geometry.Moves.phaseEdges,List.map_append,List.sum_append] at childBill
    change calls false + calls true ≤ _ at childBill
    have budget (s : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V))) (done)
        (b : s.cost ≤ phaseCost done) : s.cost ≤ work done + calls done := by
      simpa only [phaseCost,work,calls,Nat.add_right_comm] using b
    have firstBound := budget left false leftCost
    have lastBound := budget right true rightCost
    change middle.cost ≤ scatterCost at midCost
    dsimp only [scatterCost] at midCost
    change left.cost + middle.cost + 1 + right.cost + 1 ≤
      (scalar (gates false)+scalar (gates true)+moves+C+11)*V + _ + _ + _
    simp only [Nat.add_mul]
    have before := overhead false
    have after := overhead true
    omega
  · intro data g z
    let x := left.transform data
    let y := middle.transform x
    change phaseRead owner (right.transform y) (labelSpectator g z) = _
    rw [last,labelScatter_read x y (midRead x) g z]
    exact congrArg (fun bank => labelPhase w (gates true) (current true) (labelScatter n bank g))
      (funext (fun h => first data (labelSpectator h z)))
  · intro data
    exact ⟨_,_,⟨first data,leftOff data⟩,midRead _,last _,rightOff _⟩

theorem copySchedule_other {n : Fin 9} {r : Fin 32} {d : Fin 5} {w B K : ℕ}
    {ls : List Copy.Lifecycle} {x y} (steps : CopyScheduleEffect n r d w B K ls x y)
    (i : Fin 142081) (live : i ≠ Fin.last 142080) (outside : ∀ j, ownerTape n r d j ≠ i) :
    y i = x i := by
  induction ls generalizing x with
  | nil => exact congrFun steps.symm i
  | cons l ls ih =>
    obtain ⟨mid,step,rest⟩ := steps
    exact (ih rest).trans (step.2.1 i live (outside _).symm (by
      rintro mem
      obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
      exact outside _ eq))

/-- Register action of one scheduled class run at every matrix label,
including preservation of every live role outside its owner set. -/
def InvocationEffect (n : Fin 9) (r : Fin 32) (d : Fin 5) (w B K : ℕ)
    (x y : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
  (∀ g (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B),
    phaseRead owner y (labelSpectator g z) =
      labelPhase w (sectionB ++ sectionC) (Frames.scatterFinish Frames.beforeScatter)
        (labelScatter n (fun h => labelPhase w (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)
          (phaseRead owner x (labelSpectator h z))) g)) ∧
    ∀ i, i ≠ Fin.last 142080 → (∀ j, owner j ≠ i) → y i = x i

/-- At each label the physical invocation ends in the certified final frames.
The omitted zero-rank alignment leaves the represented bank unchanged. -/
theorem InvocationEffect.finalRead {n : Fin 9} {r : Fin 32} {d : Fin 5} {w B K : ℕ} {x y}
    (act : InvocationEffect n r d w B K x y) (g) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let frame := selectedFrame w
    let before := fun h => labelPhase w (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)
      (phaseRead owner x (labelSpectator h z))
    let stored := FramedCircuit.decode (fun i => frame (Frames.scatterFinish Frames.beforeScatter i))
      (labelScatter n before g)
    phaseRead owner y (labelSpectator g z) =
      FramedCircuit.encode (fun i => frame (Frames.snapshot Frames.finalRefs i))
        (FramedCircuit.moduleRun ((sectionB ++ sectionC).map RawGate.toCircuit) stored) := by
  intro owner frame before stored
  let output := FramedCircuit.moduleRun ((sectionB ++ sectionC).map RawGate.toCircuit) stored
  have aligned := Frames.final_alignment_compiled frame output
  have fixed := final_alignment_identity w frame (FramedCircuit.encode
    (fun i => frame (Frames.snapshot Frames.after234 i)) output)
  rw [runPhase_eq _ frame (modular_scatter w).choose_spec.1 _ _
    (Frames.final_alignment_pairs _) Geometry.Moves.final_checked.1] at fixed
  have read := act.1 g z
  change phaseRead owner y (labelSpectator g z) = FramedCircuit.encode
    (fun i => frame (Frames.run (sectionB ++ sectionC) (Frames.scatterFinish Frames.beforeScatter) i)) output at read
  rw [Frames.after_scatter] at read
  exact read.trans (fixed.symm.trans aligned)

/-- The decoded physical output differs from the literal scalar word exactly
by the discrepancy at scatter. Every source and helper has zero discrepancy. -/
theorem InvocationEffect.endpoint {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y) (g)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let initial := fun h => FramedCircuit.decode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (phaseRead owner x (labelSpectator h z))
    let prepared := fun h => FramedCircuit.moduleRun ((sectionD++sectionA).map RawGate.toCircuit) (initial h)
    let frame := fun j => selectedFrame w (Frames.beforeScatter j)
    let routed := FramedCircuit.decode frame (labelScatter n (fun h => FramedCircuit.encode frame (prepared h)) g)
    let localRun := FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit) (prepared g)
    let delta := routed - localRun
    (∀ j, j < 111 ∨ 222 ≤ j → delta j = 0) ∧
      phaseRead owner y (labelSpectator g z) = FramedCircuit.encode
        (fun j => selectedFrame w (Frames.snapshot Frames.finalRefs j))
        (FramedCircuit.moduleRun (program.map RawGate.toCircuit) (initial g) + delta) := by
  intro owner initial prepared frame routed localRun delta
  have zero (j : ℕ) (outside : j < 111 ∨ 222 ≤ j) : delta j = 0 := by
    have localRead : localRun j = prepared g j := by
      apply FramedCircuit.moduleRun_preserves
      intro gate mem
      obtain ⟨raw,scheduled,rfl⟩ := List.mem_map.mp mem
      have h := of_decide_eq_true (List.all_eq_true.mp scatter_target_range raw scheduled)
      change raw.target ≠ j
      omega
    change routed j - localRun j = 0
    rw [localRead,sub_eq_zero]
    by_cases low : j < 661
    · change (frame j).symm (labelScatter n _ g j) = _
      rw [labelScatter_other n _ g ⟨j,low⟩ outside]
      exact (frame j).symm_apply_apply _
    · have high := Framed.moduleRun_high _ Framed.sectionDA_target_lt (initial g) j (by omega)
      change routed j = FramedCircuit.moduleRun _ (initial g) j
      rw [high]
      simp [routed,initial,FramedCircuit.decode,labelScatter,phaseRead,Copy.extendStored,low]
  refine ⟨zero,?_⟩
  have finish := act.finalRead g z
  dsimp only at finish
  simp only [labelPhase,Frames.before_scatter] at finish
  change phaseRead owner y _ = FramedCircuit.encode _
    (FramedCircuit.moduleRun ((sectionB++sectionC).map RawGate.toCircuit) routed) at finish
  rw [finish]
  apply congrArg
  have shift := afterScatter_shift localRun delta zero
  rw [show localRun + delta = routed by dsimp [delta]; abel] at shift
  rw [shift]
  simp only [localRun,prepared,program,List.map_append,Framed.moduleRun_append]

/-- At every physical label, each source and helper returns its own
original dirty stream, expressed in its certified final frame. -/
theorem InvocationEffect.otherRead {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y) (g)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661)
    (outside : i.val < 111 ∨ 222 ≤ i.val) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let j := labelSpectator g z
    phaseRead owner y j i.val = selectedFrame w (Frames.finalRefs i.val)
      ((selectedFrame w (Frames.initialRefs i.val)).symm (phaseRead owner x j i.val)) := by
  intro owner j
  let initial := FramedCircuit.decode (fun a => selectedFrame w (Frames.snapshot Frames.initialRefs a))
    (phaseRead owner x j)
  obtain ⟨zero,finish⟩ := act.endpoint g z
  rw [finish]
  change selectedFrame w (Frames.snapshot Frames.finalRefs i.val)
    (FramedCircuit.moduleRun (program.map RawGate.toCircuit) initial i.val + _) = _
  rw [zero i.val outside,add_zero]
  rw [Frames.snapshot,ite_eq_left i.isLt]
  apply congrArg (selectedFrame w (Frames.finalRefs i.val))
  change FramedCircuit.moduleRun (program.map RawGate.toCircuit) initial i.val = _
  funext a
  rw [FramedCircuit.moduleRun_pointwise]
  let stored := fun k : Fin 661 => initial k.val a
  have bounded : (fun k => initial k a) = extendInput stored := by
    funext k
    by_cases low : k < 661
    · simp [extendInput,low,stored]
    · simp [initial,FramedCircuit.decode,phaseRead,Copy.extendStored,extendInput,low]
  rw [bounded,dirty_endpoint]
  simp only [show ¬(111 ≤ i.val ∧ i.val < 222) by omega,↓reduceDIte]
  simp only [stored,initial,FramedCircuit.decode,Frames.snapshot,ite_eq_left i.isLt]

/-- Exact dirty target endpoint: the incoming target, its paired source,
and the chart-dependent differences from the incident retained helpers. -/
theorem InvocationEffect.targetRead {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y) (g)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let initial := fun h => FramedCircuit.decode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (phaseRead owner x (labelSpectator h z))
    let prepared := fun h => FramedCircuit.moduleRun ((sectionD++sectionA).map RawGate.toCircuit) (initial h)
    let i : Fin 661 := ⟨111+t.val,by omega⟩
    let base := g*(registerChart w n i.val).transpose
    phaseRead owner y (labelSpectator g z) i.val = selectedFrame w (Frames.finalRefs i.val)
      (initial g i.val + initial g t.val + ((Copy.lifecycles.filter (fun l => i.val ∈ l.targets)).map
        (fun l => prepared (base*registerChart w n l.source) l.source - prepared g l.source)).sum) := by
  intro owner initial prepared i base
  have high (j : ℕ) (hj : 661 ≤ j) : initial g j = 0 := by
    simp [initial,FramedCircuit.decode,phaseRead,Copy.extendStored,show ¬ j < 661 by omega]
  have diff := labelScatter_difference n prepared g i (fun j hj =>
    (Framed.moduleRun_high _ Framed.sectionDA_target_lt (initial g) j hj).trans (high j hj))
  have scalar : FramedCircuit.moduleRun (program.map RawGate.toCircuit) (initial g) i.val =
      initial g i.val + initial g t.val := by
    funext a
    rw [FramedCircuit.moduleRun_pointwise]
    let stored := fun k : Fin 661 => initial g k.val a
    have bounded : (fun j => initial g j a) = extendInput stored := by
      funext j
      by_cases low : j < 661 <;> simp [extendInput,stored,low]
      rw [high j (by omega)]
      rfl
    rw [bounded]
    exact targets_added stored t
  rw [(act.endpoint g z).2]
  change selectedFrame w (Frames.snapshot Frames.finalRefs i.val)
    (FramedCircuit.moduleRun (program.map RawGate.toCircuit) (initial g) i.val + _) = _
  rw [Frames.snapshot,ite_eq_left i.isLt,scalar]
  exact congrArg (fun term => selectedFrame w (Frames.finalRefs i.val)
    (initial g i.val + initial g t.val + term)) diff

open BinaryScalarReplay in
private theorem prepared_read {Ω : Type*} (x : ℕ → Ω → ZMod 2) (high : ∀ j, 661 ≤ j → x j = 0)
    (j : ℕ) (a : Ω) :
    FramedCircuit.moduleRun ((sectionD++sectionA).map RawGate.toCircuit) x j a =
      eval (snapshot maskBank refsAfter091 j) (fun k => x k.val a) := by
  let stored := fun k : Fin 661 => x k.val a
  have bounded : (fun k => x k a) = extendInput stored := by
    funext k
    by_cases low : k < 661
    · simp [extendInput,stored,low]
    · simp [extendInput,low,high k (by omega)]
  rw [FramedCircuit.moduleRun_pointwise,bounded,← eval_start,← eval_replay,replay_append,replaySectionD]
  have link : snapshot maskBank refsAfter004 = snapshot maskBank refsBefore005 := rfl
  rw [link,replaySectionA]

/-- The retained-input columns of the nine prepared rows form an identity
matrix. In particular the nine dirty helper streams can vary independently. -/
private theorem retained_diagonal (l : Copy.Lifecycle) (hl : l ∈ Copy.lifecycles)
    (j : ℕ) (hj : j ∈ Frames.retained) :
    (snapshot maskBank refsAfter091 l.source).getLsbD j = decide (j = l.source) := by
  have checked : Copy.lifecycles.all (fun a => Frames.retained.all fun k =>
      decide ((snapshot maskBank refsAfter091 a.source).getLsbD k = decide (k = a.source))) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked l hl) j hj)

open BinaryScalarReplay in
/-- With arbitrary dirty data on the nine retained helpers alone, preparation
returns each of those inputs verbatim at its own register. -/
private theorem prepared_retained {Ω : Type*} (x : ℕ → Ω → ZMod 2)
    (supported : ∀ j, j ∉ Frames.retained → x j = 0)
    (l : Copy.Lifecycle) (hl : l ∈ Copy.lifecycles) :
    FramedCircuit.moduleRun ((sectionD++sectionA).map RawGate.toCircuit) x l.source = x l.source := by
  have bounded : ∀ j ∈ Frames.retained, j < 661 := by decide
  have mem : l.source ∈ Frames.retained := Copy.source_order ▸ List.mem_map_of_mem (f := Copy.Lifecycle.source) hl
  let k : Fin 661 := ⟨l.source,bounded _ mem⟩
  funext a
  rw [prepared_read x (fun j hj => supported j (fun h => (Nat.not_lt_of_ge hj) (bounded j h)))]
  unfold eval
  rw [Finset.sum_eq_single k]
  · simp [k,retained_diagonal l hl _ mem]
  · intro j _ ne
    by_cases hj : j.val ∈ Frames.retained
    · rw [retained_diagonal l hl _ hj]
      simp [show j.val ≠ l.source from fun eq => ne (Fin.ext eq)]
    · simp [supported _ hj]
  · simp

/-- On retained-helper inputs the target reads precisely the differences
between the routed and local dirty helpers. This isolates the part of the
endpoint that a cover representation must cancel for arbitrary helpers. -/
theorem InvocationEffect.targetRead_retained {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y) (g)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let initial := fun h => FramedCircuit.decode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (phaseRead owner x (labelSpectator h z))
    let i : Fin 661 := ⟨111+t.val,by omega⟩
    let base := g*(registerChart w n i.val).transpose
    (∀ h j, j ∉ Frames.retained → initial h j = 0) →
    phaseRead owner y (labelSpectator g z) i.val = selectedFrame w (Frames.finalRefs i.val)
      (((Copy.lifecycles.filter (fun l => i.val ∈ l.targets)).map
        (fun l => initial (base*registerChart w n l.source) l.source - initial g l.source)).sum) := by
  intro owner initial i base supported
  have helpers : ∀ j ∈ Frames.retained, 222 ≤ j := by decide
  have target : initial g i.val = 0 := supported _ _ (fun h => by
    have bound := helpers _ h
    change 222 ≤ 111+t.val at bound
    omega)
  have source : initial g t.val = 0 := supported _ _ (fun h => by have := helpers _ h; omega)
  rw [act.targetRead g z t]
  change selectedFrame w (Frames.finalRefs i.val) (initial g i.val + initial g t.val + _) = _
  rw [source,target,zero_add,zero_add]
  apply congrArg (selectedFrame w (Frames.finalRefs i.val))
  apply congrArg List.sum
  apply List.map_congr_left
  intro l hl
  have mem := (List.mem_filter.mp hl).1
  exact congrArg₂ (· - ·) (prepared_retained _ (supported _) l mem) (prepared_retained _ (supported _) l mem)

private theorem retained_support (l : Copy.Lifecycle) (hl : l ∈ Copy.lifecycles) (k : Fin 661)
    (mem : (snapshot maskBank refsAfter091 l.source).getLsbD k.val = true) :
    k.val < 111 ∨ 222 ≤ k.val := by
  have checked : Copy.lifecycles.all (fun a =>
      decide ((snapshot maskBank refsAfter091 a.source).extractLsb' 111 111 = 0)) = true := by decide +kernel
  have empty := of_decide_eq_true (List.all_eq_true.mp checked l hl)
  by_contra! h
  have bit := congrArg (fun row : BitVec 111 => row.getLsbD (k.val-111)) empty
  simp only [BitVec.getLsbD_extractLsb',show k.val-111 < 111 by omega,decide_true,Bool.true_and,
    show 111+(k.val-111) = k.val by omega,mem] at bit
  simp [BitVec.getLsbD] at bit

open BinaryScalarReplay in
/-- The target receives exactly its original stream plus its source whenever
the decoded inputs agree on the support of each incident retained row at
the two labels used for that row. Other inputs may differ arbitrarily. -/
theorem InvocationEffect.targetRead_of_support {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y) (g)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let initial := fun h => FramedCircuit.decode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (phaseRead owner x (labelSpectator h z))
    let i : Fin 661 := ⟨111+t.val,by omega⟩
    let base := g*(registerChart w n i.val).transpose
    (∀ l ∈ Copy.lifecycles, i.val ∈ l.targets → ∀ k : Fin 661,
      (k.val < 111 ∨ 222 ≤ k.val) →
      (snapshot maskBank refsAfter091 l.source).getLsbD k.val = true →
      initial (base*registerChart w n l.source) k.val = initial g k.val) →
    phaseRead owner y (labelSpectator g z) i.val =
      selectedFrame w (Frames.finalRefs i.val) (initial g i.val + initial g t.val) := by
  intro owner initial i base agree
  have high (h) (j : ℕ) (hj : 661 ≤ j) : initial h j = 0 := by
    simp [initial,FramedCircuit.decode,phaseRead,Copy.extendStored,show ¬ j < 661 by omega]
  let prepared := fun h => FramedCircuit.moduleRun ((sectionD++sectionA).map RawGate.toCircuit) (initial h)
  have same (l : Copy.Lifecycle) (hl : l ∈ Copy.lifecycles) (hit : i.val ∈ l.targets) :
      prepared (base*registerChart w n l.source) l.source = prepared g l.source := by
    funext a
    simp only [prepared,prepared_read _ (high _),eval]
    apply Finset.sum_congr rfl
    intro k _
    by_cases mem : (snapshot maskBank refsAfter091 l.source).getLsbD k.val = true
    · simp only [mem,ite_true,agree l hl hit k (retained_support l hl k mem) mem]
    · rw [ite_eq_right mem,ite_eq_right mem]
  have correction : (((Copy.lifecycles.filter (fun l => i.val ∈ l.targets)).map
      (fun l => prepared (base*registerChart w n l.source) l.source - prepared g l.source))).sum = 0 := by
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hv
    have hit := List.mem_filter.mp hl
    rw [same l hit.1 (by simpa using hit.2),sub_self]
  rw [act.targetRead g z t]
  exact congrArg (selectedFrame w (Frames.finalRefs i.val))
    ((congrArg (initial g i.val + initial g t.val + ·) correction).trans (add_zero _))

private theorem registerChart_gram (w : ℕ) (n : Fin 9) (a b : ℕ)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) :
    let h := g*(registerChart w n a).transpose*registerChart w n b
    h*h.transpose = g*g.transpose := by
  intro h
  simp only [h,Matrix.transpose_mul,Matrix.transpose_transpose]
  rw [Matrix.mul_assoc,← Matrix.mul_assoc (registerChart w n b),
    mul_eq_one_comm.mp (registerChart_inverse w n b),Matrix.one_mul,
    Matrix.mul_assoc,← Matrix.mul_assoc (registerChart w n a).transpose,
    registerChart_inverse,Matrix.one_mul]

/-- Each live Gram class may carry its own independent dirty register bank. -/
theorem InvocationEffect.gramEndpoint {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B)
    (stored : Fin 661 → AddressStream (ZMod (prime^w))) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    ∀ g : Cover.LabelPadding.Label 64 w, IsUnit g → (∀ h, IsUnit h → h*h.transpose = g*g.transpose → ∀ j : Fin 661, phaseRead owner x (labelSpectator h z) j.val =
      selectedFrame w (Frames.initialRefs j.val) (stored j)) →
    ∀ i : Fin 661, phaseRead owner y (labelSpectator g z) i.val =
      selectedFrame w (Frames.finalRefs i.val)
        (if hit : 111 ≤ i.val ∧ i.val < 222 then stored i + stored ⟨i.val-111,by omega⟩ else stored i) := by
  intro owner g live input i
  let initial := fun h => FramedCircuit.decode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
    (phaseRead owner x (labelSpectator h z))
  have decode (h) (unit : IsUnit h) (gram : h*h.transpose = g*g.transpose) (j : Fin 661) : initial h j.val = stored j := by
    simp only [initial,FramedCircuit.decode,Frames.snapshot,ite_eq_left j.isLt,input h unit gram j,
      LinearEquiv.symm_apply_apply]
  by_cases hit : 111 ≤ i.val ∧ i.val < 222
  · let t : Fin 111 := ⟨i.val-111,by omega⟩
    have index : 111+t.val = i.val := by dsimp [t]; omega
    let target : Fin 661 := ⟨111+t.val,by omega⟩
    have same : target = i := Fin.ext index
    have eq := act.targetRead_of_support g z t
    dsimp only at eq
    have compatible (l : Copy.Lifecycle) (_hl : l ∈ Copy.lifecycles) (_target : target.val ∈ l.targets)
        (k : Fin 661) (_range : k.val < 111 ∨ 222 ≤ k.val)
        (_mem : (snapshot maskBank refsAfter091 l.source).getLsbD k.val = true) :
        initial (g*(registerChart w n target.val).transpose*registerChart w n l.source) k.val = initial g k.val := by
      have unit (j : ℕ) := isUnit_iff_exists_inv.mpr ⟨_,registerChart_inverse w n j⟩
      have back := isUnit_iff_exists_inv.mpr ⟨_,mul_eq_one_comm.mp (registerChart_inverse w n l.source)⟩
      exact (decode _ ((live.mul (unit target.val)).mul back) (registerChart_gram _ _ _ _ _) k).trans (decode g live rfl k).symm
    have read := eq compatible
    change phaseRead owner y (labelSpectator g z) target.val = selectedFrame w (Frames.finalRefs target.val)
      (initial g target.val + initial g t.val) at read
    rw [same,decode g live rfl i,decode g live rfl (⟨t.val,by omega⟩ : Fin 661)] at read
    simpa only [dite_eq_left hit] using read
  · rw [dite_eq_right hit,act.otherRead g z i (by omega),input g live rfl i,LinearEquiv.symm_apply_apply]

/-- A replicated input stream on live cover labels stays replicated through
one complete invocation. Singular padding is arbitrary, since the relative
charts in each COPY window preserve invertibility. -/
theorem InvocationEffect.liveEndpoint {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B)
    (stored : Fin 661 → AddressStream (ZMod (prime^w))) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    (∀ h, IsUnit h → ∀ j : Fin 661, phaseRead owner x (labelSpectator h z) j.val =
      selectedFrame w (Frames.initialRefs j.val) (stored j)) →
    ∀ g, IsUnit g → ∀ i : Fin 661, phaseRead owner y (labelSpectator g z) i.val =
      selectedFrame w (Frames.finalRefs i.val)
        (if hit : 111 ≤ i.val ∧ i.val < 222 then stored i + stored ⟨i.val-111,by omega⟩ else stored i) := by
  intro owner input g live
  exact act.gramEndpoint z stored g live (fun h unit _ => input h unit)

private theorem InvocationEffect.targetRead_permutation {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) :
    let R := Matrix (Fin 64) (Fin 64) (ZMod (prime^w))
    ∀ {Labels : Type} [Fintype Labels] (label : Labels → R),
    (∀ l : Copy.Lifecycle, ∃ perm : Labels ≃ Labels, ∀ g, label (perm g) =
      label g*(registerChart w n (111+t.val)).transpose*registerChart w n l.source) →
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let initial := fun h => FramedCircuit.decode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (phaseRead owner x (labelSpectator h z))
    let i : Fin 661 := ⟨111+t.val,by omega⟩
    (∑ g : Labels, phaseRead owner y (labelSpectator (label g) z) i.val) =
      selectedFrame w (Frames.finalRefs i.val)
        ((∑ g : Labels, initial (label g) i.val) + ∑ g : Labels, initial (label g) t.val) := by
  classical
  intro R Labels inst label permutes owner initial i
  let prep := fun h => FramedCircuit.moduleRun ((sectionD++sectionA).map RawGate.toCircuit) (initial h)
  let windows := Copy.lifecycles.filter (fun l => i.val ∈ l.targets)
  let diff := fun (l : Copy.Lifecycle) (g : Labels) =>
    prep ((label g)*(registerChart w n i.val).transpose*registerChart w n l.source) l.source - prep (label g) l.source
  have cancel (l : Copy.Lifecycle) : ∑ g : Labels, diff l g = 0 := by
    obtain ⟨perm,action⟩ := permutes l
    unfold diff
    rw [Finset.sum_sub_distrib,sub_eq_zero]
    calc
      _ = ∑ g : Labels, prep (label (perm g)) l.source :=
        Finset.sum_congr rfl (fun g _ => congrArg (fun h => prep h l.source) (action g).symm)
      _ = _ := Equiv.sum_comp perm (fun g => prep (label g) l.source)
  have allWindows (ls : List Copy.Lifecycle) :
      (∑ g : Labels, (ls.map (fun l => diff l g)).sum) = 0 := by
    induction ls with
    | nil => simp
    | cons l ls ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,cancel,ih,add_zero]
  have atLabel (g : Labels) := act.targetRead (label g) z t
  calc
    _ = ∑ g : Labels, selectedFrame w (Frames.finalRefs i.val)
        (initial (label g) i.val + initial (label g) t.val + (windows.map (fun l => diff l g)).sum) :=
      Finset.sum_congr rfl (fun g _ => atLabel g)
    _ = _ := by rw [← map_sum,Finset.sum_add_distrib,Finset.sum_add_distrib,allWindows,add_zero]

/-- Each relative COPY chart is orthogonal, so it preserves the row Gram
matrix of a live label. Every union of Gram classes therefore has its
own aggregate endpoint, including the full set of live labels. -/
theorem InvocationEffect.targetRead_sum {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) :
    let R := Matrix (Fin 64) (Fin 64) (ZMod (prime^w))
    ∀ keep : R → Bool,
    let Labels := {g : Rˣ // keep (g.val*g.val.transpose) = true}
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let initial := fun h => FramedCircuit.decode (fun j => selectedFrame w (Frames.snapshot Frames.initialRefs j))
      (phaseRead owner x (labelSpectator h z))
    let i : Fin 661 := ⟨111+t.val,by omega⟩
    (∑ g : Labels, phaseRead owner y (labelSpectator g.val.val z) i.val) =
      selectedFrame w (Frames.finalRefs i.val)
        ((∑ g : Labels, initial g.val.val i.val) + ∑ g : Labels, initial g.val.val t.val) := by
  classical
  intro R keep Labels owner initial i
  apply act.targetRead_permutation z t (fun g : Labels => g.val.val)
  intro l
  let chart (j : ℕ) : Rˣ := ⟨registerChart w n j,(registerChart w n j).transpose,
    mul_eq_one_comm.mp (registerChart_inverse w n j),registerChart_inverse w n j⟩
  let route := (chart i.val)⁻¹ * chart l.source
  have gram (g : Rˣ) : (g*route).val*(g*route).val.transpose = g.val*g.val.transpose := by
    change (g.val*((registerChart w n i.val).transpose*registerChart w n l.source))*
      (g.val*((registerChart w n i.val).transpose*registerChart w n l.source)).transpose = _
    rw [← Matrix.mul_assoc]
    exact registerChart_gram _ _ _ _ _
  let permute : Labels ≃ Labels := (Equiv.mulRight route).subtypeEquiv (fun g => by
    change keep (g.val*g.val.transpose) = true ↔ keep ((g*route).val*(g*route).val.transpose) = true
    rw [gram])
  refine ⟨permute,fun g => ?_⟩
  change g.val.val*((registerChart w n i.val).transpose*registerChart w n l.source) = _
  rw [Matrix.mul_assoc]

/-- Every physical matrix row, including singular padding, contributes to
this sum. Recovery can therefore scan the label box without a class test. -/
theorem InvocationEffect.targetRead_box {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) :
    let R := Cover.LabelPadding.Label 64 w
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let total := fun j => ∑ g : R, phaseRead owner x (labelSpectator g z) j
    let initial := fun j => (selectedFrame w (Frames.initialRefs j)).symm (total j)
    (∑ g : R, phaseRead owner y (labelSpectator g z) (111+t.val)) =
      selectedFrame w (Frames.finalRefs (111+t.val)) (initial (111+t.val) + initial t.val) := by
  classical
  intro R owner total initial
  have permutes (l : Copy.Lifecycle) :
      ∃ perm : R ≃ R, ∀ g, perm g = g*(registerChart w n (111+t.val)).transpose*registerChart w n l.source := by
    let A := registerChart w n (111+t.val)
    let B := registerChart w n l.source
    have left := registerChart_inverse w n (111+t.val)
    have right := registerChart_inverse w n l.source
    change A.transpose*A = 1 at left
    change B.transpose*B = 1 at right
    refine ⟨⟨fun g => g*A.transpose*B,fun g => g*B.transpose*A,?_,?_⟩,fun _ => rfl⟩
    · intro g
      change g*A.transpose*B*B.transpose*A = g
      rw [Matrix.mul_assoc (g*A.transpose) B,mul_eq_one_comm.mp right,Matrix.mul_one,Matrix.mul_assoc,left,Matrix.mul_one]
    · intro g
      change g*B.transpose*A*A.transpose*B = g
      rw [Matrix.mul_assoc (g*B.transpose) A,mul_eq_one_comm.mp left,Matrix.mul_one,Matrix.mul_assoc,right,Matrix.mul_one]
  have read := act.targetRead_permutation z t (fun g : R => g) permutes
  dsimp only at read
  simpa only [initial,total,FramedCircuit.decode,Frames.snapshot,
    ite_eq_left (show 111+t.val < 661 by omega),ite_eq_left (show t.val < 661 by omega),map_sum,owner] using read

/-- The complete invocation acts on a Gram-class sum just as the scalar
word acts on the decoded input sums, for every retained register. -/
theorem InvocationEffect.sumEndpoint {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661) :
    let R := Cover.LabelPadding.Label 64 w
    ∀ keep : R → Bool,
    let Labels := {g : Rˣ // keep (g.val*g.val.transpose) = true}
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let total := fun j => ∑ g : Labels, phaseRead owner x (labelSpectator g.val.val z) j
    let initial := fun j => (selectedFrame w (Frames.initialRefs j)).symm (total j)
    (∑ g : Labels, phaseRead owner y (labelSpectator g.val.val z) i.val) =
      selectedFrame w (Frames.finalRefs i.val)
        (if 111 ≤ i.val ∧ i.val < 222 then initial i.val + initial (i.val-111) else initial i.val) := by
  intro R keep Labels owner total initial
  by_cases hit : 111 ≤ i.val ∧ i.val < 222
  · let t : Fin 111 := ⟨i.val-111,by omega⟩
    have index : 111+t.val = i.val := by dsimp [t]; omega
    have target := act.targetRead_sum z t keep
    dsimp only at target
    rw [index] at target
    rw [target,ite_eq_left hit]
    apply congrArg (selectedFrame w (Frames.finalRefs i.val))
    simp only [FramedCircuit.decode,Frames.snapshot,ite_eq_left i.isLt,
      ite_eq_left (show t.val < 661 by omega),initial,total,map_sum,t]
    rfl
  · rw [ite_eq_right hit]
    simp only [initial,total,map_sum]
    exact Finset.sum_congr rfl (fun g _ => act.otherRead g.val.val z i (by omega))

/-- Place a bank in one physical label row of each inherited block,
preserving the active address and trailing spectator. -/
noncomputable def singleLabelBank {w B K : ℕ} (label : Cover.LabelPadding.Label 64 w)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2)
    (i : Fin 142081) (p : Fin ((prime^w)^16*(B*prime^(64*(w*64))*K))) : ZMod 2 :=
  let active := finProdFinEquiv.symm p
  let tail : Fin (B*prime^(64*(w*64))) × Fin K := finProdFinEquiv.symm active.2
  let block : Fin B × Fin (prime^(64*(w*64))) := finProdFinEquiv.symm tail.1
  if block.2.val = (Cover.LabelAddress.address label).val then
    x i (finProdFinEquiv (active.1,finProdFinEquiv (block.1,tail.2))) else 0

/-- XOR the full matrix box at a fixed active address, inherited block and
trailing spectator, in the physical row numbering. -/
noncomputable def collapseLabelBank {w B K : ℕ}
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (i : Fin 142081) (p : Fin ((prime^w)^16*(B*K))) : ZMod 2 :=
  let active : Fin ((prime^w)^16) × Fin (B*K) := finProdFinEquiv.symm p
  let block : Fin B × Fin K := finProdFinEquiv.symm active.2
  ∑ row : Fin (prime^(64*(w*64))), x i
    (finProdFinEquiv (active.1,finProdFinEquiv (finProdFinEquiv (block.1,row),block.2)))

/-- Summing the one-block scan bills over all active addresses and inherited
blocks charges exactly 111 passes over one role in the represented parent. -/
theorem collapseLabelBlock_parentBill (v : RecursiveInterchangeLayout.Descriptor) (w B rows : ℕ)
    (width : v.width = 64*w) (split : v.rows = 142080*rows)
    (labels : v.beforeH = B*prime^(64*(w*64))) :
    let K := (prime^w)^112*(v.beforeRows*rows*v.between*v.afterD)
    (prime^w)^16*B*(111*(prime^(64*(w*64))*K))*142080 =
      111*RecursiveInterchangeLayout.volume prime v := by
  intro K
  have size := (copyChild_measures v w rows width split).2
  rw [copyChild_volume,labels] at size
  rw [← size]
  dsimp only [K]
  ac_rfl

/-- Scan all physical label rows of one active address and inherited block.
The result is the complete collapsed spectator record at linear volume cost. -/
theorem collapseLabelBlock_run {w B K : ℕ} (hK : 0 < K)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (i : Fin 142081) (a : Fin ((prime^w)^16)) (b : Fin B) (v : Tapes 2 prime) :
    let N := prime^(64*(w*64))
    let bits := FlatCoordinateSchedule.bits
    (∀ (row : Fin N) (j : Fin K), v.tape 0 (v.head 0+row.val*K+j.val) = SparseRoleCircuit.encode
      (x i (finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,row),j))))) →
    (∀ j : Fin K, v.tape 1 (v.head 1+j.val) = SparseRoleCircuit.encode 0) →
    ∃ out, HoareTime (LabelRowXor.program prime) (fun s => s = LabelRowXor.bank v (bits K) (bits N))
        (fun s => s = LabelRowXor.bank out (bits K) (bits N)) (111*(N*K)) ∧
      out.head 0 = v.head 0 + N*K ∧ out.head 1 = v.head 1 ∧ out.tape 0 = v.tape 0 ∧
      (∀ j : Fin K, out.tape 1 (v.head 1+j.val) = SparseRoleCircuit.encode
        (collapseLabelBank x i (finProdFinEquiv (a,finProdFinEquiv (b,j))))) ∧
      ∀ z, ¬(v.head 1 ≤ z ∧ z < v.head 1+K) → out.tape 1 z = v.tape 1 z := by
  intro N bits input zero
  obtain ⟨out,run,hsrc,hdst,src,acc,off⟩ := LabelRowXor.run v (bits K) (bits N) K N
    (FlatCoordinateSchedule.bits_value K) (FlatCoordinateSchedule.bits_value N) _ (fun _ => 0) input zero
  refine ⟨out,run.consequence (fun _ h => h) (fun _ h => h) ?_,hsrc,hdst,src,?_,off⟩
  · have hn : 0 < N := pow_pos Shared50ModularControl.prime_prime.pos _
    have width := FlatCoordinateDimensions.bits_length_le_twice (Nat.le_refl K) hK
    have count := FlatCoordinateDimensions.bits_length_le_twice (Nat.le_refl N) hn
    have scan := Nat.mul_le_mul_left N (show 14*K+14*(bits K).length+39 ≤ 81*K by
      change 14*K+14*(FlatCoordinateSchedule.bits K).length+39 ≤ 81*K
      omega)
    have volume := Nat.le_mul_of_pos_right N hK
    change N*(14*K+14*(FlatCoordinateSchedule.bits K).length+39)+7*(FlatCoordinateSchedule.bits N).length+16 ≤ _
    dsimp only [bits] at scan
    rw [show N*(81*K) = 81*(N*K) by ring] at scan
    omega
  · intro j
    simpa only [collapseLabelBank,Equiv.symm_apply_apply,zero_add] using acc j

theorem collapse_singleLabelBank {w B K : ℕ} (label : Cover.LabelPadding.Label 64 w)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2) :
    collapseLabelBank (singleLabelBank label x) = x := by
  classical
  funext i p
  obtain ⟨⟨a,tail⟩,rfl⟩ := (finProdFinEquiv : Fin ((prime^w)^16) × Fin (B*K) ≃ _).surjective p
  obtain ⟨⟨b,k⟩,rfl⟩ := (finProdFinEquiv : Fin B × Fin K ≃ _).surjective tail
  have count : (prime^w)^(64*64) = prime^(64*(w*64)) := by rw [← pow_mul]; congr 1; omega
  let row := (Cover.LabelAddress.address label).cast count
  simp only [collapseLabelBank,singleLabelBank,Equiv.symm_apply_apply]
  rw [Finset.sum_eq_single row]
  · simp [row]
  · intro j _ ne
    have different : j.val ≠ row.val := fun eq => ne (Fin.ext eq)
    simp only [row,Fin.val_cast] at different
    simp only [ite_eq_right different]
  · simp

private theorem labelRowCount (w : ℕ) : (prime^w)^(64*64) = prime^(64*(w*64)) := by
  rw [← pow_mul]; congr 1; omega

theorem address_bijective (w : ℕ) :
    Function.Bijective (Cover.LabelAddress.address (m := 64) (Q := prime^w)) := by
  constructor
  · intro g h heq
    ext i j
    apply ZMod.val_injective
    rw [← Cover.LabelAddress.entry g i j,← Cover.LabelAddress.entry h i j,heq]
  · intro row
    let digits := FlatCoordinateLayout.coordinates row
    refine ⟨fun i j => digits (finProdFinEquiv (j,i)),?_⟩
    unfold Cover.LabelAddress.address
    have unpack : M8.AtomOps.refine (Cover.Route.cols (fun i j => digits (finProdFinEquiv (j,i)))) = digits := by
      funext k
      simp only [Cover.Route.cols,M8.AtomOps.refine,Prod.mk.eta,Equiv.apply_symm_apply]
    rw [unpack,FlatCoordinateLayout.rank_coordinates]

private noncomputable def physicalLabelRow (w : ℕ) :
    Cover.LabelPadding.Label 64 w ≃ Fin (prime^(64*(w*64))) :=
  (Equiv.ofBijective _ (address_bijective w)).trans (finCongr (labelRowCount w))

private theorem castRow_val {α : Type*} {m n : ℕ} (f : α → Fin m) (hf : Function.Bijective f)
    (size : m = n) (g : α) : (((Equiv.ofBijective f hf).trans (finCongr size)) g).val = (f g).val := by
  subst n
  rfl

private theorem physicalLabelRow_val {w : ℕ} (g : Cover.LabelPadding.Label 64 w) :
    (physicalLabelRow w g).val = (Cover.LabelAddress.address g).val :=
  castRow_val _ (address_bijective w) (labelRowCount w) g

theorem exists_firstRowLabel (w : ℕ) :
    ∃ g : Cover.LabelPadding.Label 64 w, (Cover.LabelAddress.address g).val = 0 := by
  refine ⟨(physicalLabelRow w).symm 0, ?_⟩
  rw [← physicalLabelRow_val]
  simp

/-- The common label at physical row zero for all stages of a given width. -/
noncomputable def firstRowLabel (w : ℕ) : Cover.LabelPadding.Label 64 w :=
  (exists_firstRowLabel w).choose

/-- The ordinary one-row padding machine implements placement in physical row zero. -/
theorem singleLabelBank_pad {w B K : ℕ} :
    let label := firstRowLabel w
    ∀ (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2) i p,
      singleLabelBank label x i p =
        RecursiveRowPadding.pad (A := (prime^w)^16*B) (R := 1) (L := K)
          (prime^(64*(w*64))) 0 (fun z => x i (Fin.cast (by simp [Nat.mul_assoc]) z))
          (Fin.cast (by simp [Nat.mul_assoc]) p) := by
  intro label
  intro x i p
  have addr : (Cover.LabelAddress.address label).val = 0 := (exists_firstRowLabel w).choose_spec
  obtain ⟨⟨a,t⟩,rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨br,k⟩,rfl⟩ := finProdFinEquiv.surjective t
  obtain ⟨⟨b,r⟩,rfl⟩ := finProdFinEquiv.surjective br
  have index : Fin.cast (by simp [Nat.mul_assoc])
      (finProdFinEquiv (a,finProdFinEquiv (finProdFinEquiv (b,r),k))) =
      RecursiveInterchangeRows.pack (RecursiveInterchangeRows.pack (finProdFinEquiv (a,b)) r) k := by
    apply Fin.ext
    simp only [Fin.val_cast, RecursiveInterchangeRows.pack, finProdFinEquiv_apply_val]
    ring
  rw [index, RecursiveRowPadding.pad_entry]
  simp only [singleLabelBank, Equiv.symm_apply_apply, addr]
  by_cases h : r.val = 0
  · simp only [h, ite_true, Nat.zero_lt_one, dite_eq_left]
    apply congrArg (x i)
    apply Fin.ext
    simp only [RecursiveInterchangeRows.pack, Fin.val_cast, finProdFinEquiv_apply_val]
    simp
    ring
  · have hr : ¬ r.val < 1 := by omega
    simp [h,hr]

open RowPaddingConstructedAlphabet (bank) in
open FlatCoordinateSchedule (bits bits_value bits_canonical) in
/-- A prepared twelve-tape bank writes one padded owner at head zero in linear time. -/
theorem singleLabelBank_pad_hoare {w B K : ℕ} (hB : 0 < B) (hK : 0 < K) :
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    let label := firstRowLabel w
    ∀ (x : Fin 142081 → Fin (A*(B*K)) → ZMod 2) i,
    let word := List.ofFn (SparseRoleCircuit.encoded (a := prime) x i)
    let output := List.ofFn (SparseRoleCircuit.encoded (a := prime) (singleLabelBank label x) i)
    HoareTime RowPaddingConstructedAlphabet.program
      (fun v => v = bank (putWord (fun _ => blank) 0 word) (fun _ => blank) 0 0
        (bits (A*B)) (bits 1) (bits N) (bits K))
      (fun v => v = bank (RowPaddingConstructedAlphabet.erased (putWord (fun _ => blank) 0 word) 0 (A*(B*K)))
        (putWord (fun _ => blank) 0 output) 0 0 (bits (A*B)) (bits 1) (bits N) (bits K))
      (413*(A*B)*(N*K)) := by
  intro A N
  have placement :=  singleLabelBank_pad (w := w) (B := B) (K := K)
  intro label x i
  let hs : A*B*1*K = A*(B*K) := by simp [Nat.mul_assoc]
  let hd : A*(B*N*K) = A*B*N*K := by simp [Nat.mul_assoc]
  let source := fun z => x i (Fin.cast hs z)
  have run := RowPaddingConstructedAlphabet.pad_bits_hoare (a := prime) (fun _ => blank) (fun _ => blank)
    0 0 _ _ _ _ (A*B) 1 N K (fun z => decide (source z = 1))
    (bits_value _) (bits_value _) (bits_value _) (bits_value _)
    (bits_canonical _) (bits_canonical _) (bits_canonical _) (bits_canonical _)
    (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hB)
    Nat.zero_lt_one (pow_pos Shared50ModularControl.prime_prime.pos _) hK
  have castWord {m n : ℕ} (h : m=n) (f : Fin n → Fin (prime+4)) :
      List.ofFn (fun z => f (Fin.cast h z)) = List.ofFn f := by subst n; rfl
  have encodePad (z : Fin (A*B*N*K)) :
      SparseRoleCircuit.encode (a := prime) (RecursiveRowPadding.pad N 0 source z) =
        RecursiveRowPadding.pad N (bitSymbol false) (fun j => bitSymbol (decide (source j = 1))) z := by
    unfold RecursiveRowPadding.pad
    dsimp only
    split_ifs <;> rfl
  have output : List.ofFn (SparseRoleCircuit.encoded (a := prime) (singleLabelBank label x) i) =
      List.ofFn (RecursiveRowPadding.pad N (bitSymbol false) (fun j => bitSymbol (decide (source j = 1)))) := by
    rw [← castWord hd (RecursiveRowPadding.pad N (bitSymbol false) _)]
    apply congrArg List.ofFn
    funext z
    unfold SparseRoleCircuit.encoded
    rw [placement]
    exact encodePad (Fin.cast hd z)
  dsimp only
  have erasedLength (f : ℤ → Fin (prime+4)) :
      RowPaddingConstructedAlphabet.erased f 0 (A*(B*K)) =
      RowPaddingConstructedAlphabet.erased f 0 (A*B*1*K) := congrArg _ hs.symm
  rw [output, erasedLength, ← castWord hs (SparseRoleCircuit.encoded (a := prime) x i)]
  exact run

private theorem labelSpectator_pack {w B K : ℕ} (g : Cover.LabelPadding.Label 64 w)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) :
    labelSpectator g z = finProdFinEquiv (finProdFinEquiv (z.b,physicalLabelRow w g),(z.after : Fin K)) := by
  apply Fin.ext
  simp only [labelSpectator,finProdFinEquiv_apply_val,physicalLabelRow_val]
  exact pack z.b.val (prime^(64*(w*64))) (Cover.LabelAddress.address g).val K z.after.val
where
  pack (b N row K k : ℕ) : (b*N+row)*K+k = k+K*(row+N*b) := by ring

theorem singleLabelBank_read {w B K : ℕ} (label g : Cover.LabelPadding.Label 64 w)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2) (i : Fin 142081)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))) :
    singleLabelBank label x i (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (labelSpectator g z)) =
      if g = label then x i (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (finProdFinEquiv (z.b,z.after)))
      else 0 := by
  classical
  have count : (prime^w)^(64*64) = prime^(64*(w*64)) := by rw [← pow_mul]; congr 1; omega
  let row := (Cover.LabelAddress.address g).cast count
  let last : Fin K := z.after
  have packed : labelSpectator g z = finProdFinEquiv (finProdFinEquiv (z.b,row),last) := by
    apply Fin.ext
    simp only [labelSpectator,finProdFinEquiv_apply_val,row,Fin.val_cast]
    exact pack z.b.val (prime^(64*(w*64))) (Cover.LabelAddress.address g).val K z.after.val
  have equal : (Cover.LabelAddress.address g).val = (Cover.LabelAddress.address label).val ↔ g = label := by
    refine ⟨fun h => ?_,fun h => h ▸ rfl⟩
    ext a b
    apply ZMod.val_injective
    rw [← Cover.LabelAddress.entry g a b,← Cover.LabelAddress.entry label a b,h]
  simp only [singleLabelBank,FlatCoordinateLayout.index,packed,Equiv.symm_apply_apply,row,Fin.val_cast,equal]

  rfl
where
  pack (b N row K k : ℕ) : (b*N+row)*K+k = k+K*(row+N*b) := by ring

/-- Reading the physically collapsed tape is the sum of the matrix-indexed
reads, for the same active address, inherited block and spectator. -/
theorem collapseLabelBank_read {w B K : ℕ}
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (owner : Fin 661 ↪ Fin 142081) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661) :
    phaseRead owner (collapseLabelBank x) (finProdFinEquiv (z.b,z.after)) i.val =
      ∑ g : Cover.LabelPadding.Label 64 w, phaseRead owner x (labelSpectator g z) i.val := by
  funext s
  simp only [Finset.sum_apply,phaseRead,Copy.extendStored,dite_eq_left i.isLt,FlatCoordinateLayout.index,
    collapseLabelBank,Equiv.symm_apply_apply,labelSpectator_pack]
  exact (Equiv.sum_comp (physicalLabelRow w) (fun row => x (owner i)
    (finProdFinEquiv (FlatCoordinateLayout.rank (AffineFieldCoordinates.embed s),
      finProdFinEquiv (finProdFinEquiv (z.b,row),(z.after : Fin K)))))).symm

/-- The scan recovers each target's framed XOR from the two input scans. -/
theorem InvocationEffect.collapsedTarget {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y} (act : InvocationEffect n r d w B K x y)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (t : Fin 111) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let j : Fin (B*K) := finProdFinEquiv (z.b,z.after)
    let initial := fun i => (selectedFrame w (Frames.initialRefs i)).symm
      (phaseRead owner (collapseLabelBank x) j i)
    phaseRead owner (collapseLabelBank y) j (111+t.val) =
      selectedFrame w (Frames.finalRefs (111+t.val)) (initial (111+t.val) + initial t.val) := by
  intro owner j initial
  let dst : Fin 661 := ⟨111+t.val,by omega⟩
  let src : Fin 661 := ⟨t.val,by omega⟩
  exact (collapseLabelBank_read y owner z dst).trans ((act.targetRead_box z t).trans
    (congrArg (selectedFrame w (Frames.finalRefs dst.val)) (congrArg₂ (· + ·)
      (congrArg (selectedFrame w (Frames.initialRefs dst.val)).symm (collapseLabelBank_read x owner z dst).symm)
      (congrArg (selectedFrame w (Frames.initialRefs src.val)).symm (collapseLabelBank_read x owner z src).symm))))

/-- Summing the physical reads of a single-row encoding recovers the
original bank at every block and active address of the retained class. -/
theorem singleLabelBank_sum {w B K : ℕ} (label : (Cover.LabelPadding.Label 64 w)ˣ)
    (keep : Cover.LabelPadding.Label 64 w → Bool) (member : keep (label.val*label.val.transpose) = true)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2)
    (owner : Fin 661 ↪ Fin 142081) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661) :
    let Labels := {g : (Cover.LabelPadding.Label 64 w)ˣ // keep (g.val*g.val.transpose) = true}
    (∑ g : Labels, phaseRead owner (singleLabelBank label.val x) (labelSpectator g.val.val z) i.val) =
      phaseRead owner x (finProdFinEquiv (z.b,z.after)) i.val := by
  classical
  intro Labels
  funext s
  rw [Finset.sum_apply,Finset.sum_eq_single (⟨label,member⟩ : Labels)]
  · simp only [phaseRead,Copy.extendStored,dite_eq_left i.isLt,singleLabelBank_read,ite_true]
  · intro g _ ne
    have different : g.val.val ≠ label.val := fun eq => ne (Subtype.ext (Units.ext eq))
    simp only [phaseRead,Copy.extendStored,dite_eq_left i.isLt,singleLabelBank_read,ite_eq_right different]
  · simp

/-- Starting with a single encoded label recovers the ordinary dirty word
from the class sum of the actual invocation output. -/
theorem InvocationEffect.singleLabelEndpoint {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} (label : (Cover.LabelPadding.Label 64 w)ˣ)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*K)) → ZMod 2) {y}
    (act : InvocationEffect n r d w B K (singleLabelBank label.val x) y)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661)
    (keep : Cover.LabelPadding.Label 64 w → Bool) (member : keep (label.val*label.val.transpose) = true) :
    let Labels := {g : (Cover.LabelPadding.Label 64 w)ˣ // keep (g.val*g.val.transpose) = true}
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let input := fun j => (selectedFrame w (Frames.initialRefs j)).symm
      (phaseRead owner x (finProdFinEquiv (z.b,z.after)) j)
    (∑ g : Labels, phaseRead owner y (labelSpectator g.val.val z) i.val) =
      selectedFrame w (Frames.finalRefs i.val)
        (if 111 ≤ i.val ∧ i.val < 222 then input i.val + input (i.val-111) else input i.val) := by
  intro Labels owner input
  rw [act.sumEndpoint z i keep]
  let total := fun j => (selectedFrame w (Frames.initialRefs j)).symm
    (∑ g : Labels, phaseRead owner (singleLabelBank label.val x) (labelSpectator g.val.val z) j)
  have read (j : Fin 661) : total j.val = input j.val :=
    congrArg (selectedFrame w (Frames.initialRefs j.val)).symm (singleLabelBank_sum label keep member x owner z j)
  apply congrArg (selectedFrame w (Frames.finalRefs i.val))
  by_cases hit : 111 ≤ i.val ∧ i.val < 222
  · simp only [ite_eq_left hit]
    exact congrArg₂ (· + ·) (read i) (read ⟨i.val-111,by omega⟩)
  · exact (ite_eq_right hit).trans ((read i).trans (ite_eq_right hit).symm)

/-- On a chosen union of live Gram classes every permanent tape carries the
same stream as the reference label. Choosing one Gram class allows other
classes to store independent data. -/
def LiveReplicatedAt {w B K : ℕ} (keep : Cover.LabelPadding.Label 64 w → Prop)
    (ref : Cover.LabelPadding.Label 64 w)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  ∀ i, i ≠ Fin.last 142080 → ∀ g : Cover.LabelPadding.Label 64 w, IsUnit g → keep (g*g.transpose) →
    ∀ (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))),
      x i (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (labelSpectator g z)) =
      x i (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (labelSpectator ref z))

theorem InvocationEffect.liveReplicatedAt {n : Fin 9} {r : Fin 32} {d : Fin 5} {w B K : ℕ} {x y}
    {keep : Cover.LabelPadding.Label 64 w → Prop} {ref : Cover.LabelPadding.Label 64 w}
    (unitRef : IsUnit ref) (keepRef : keep (ref*ref.transpose))
    (act : InvocationEffect n r d w B K x y) (input : LiveReplicatedAt (B := B) (K := K) keep ref x) :
    LiveReplicatedAt (B := B) (K := K) keep ref y := by
  intro i permanent g live kept z s
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
  by_cases owned : ∃ j, owner j = i
  · obtain ⟨j,rfl⟩ := owned
    let stored := fun k : Fin 661 => (selectedFrame w (Frames.initialRefs k.val)).symm
      (phaseRead owner x (labelSpectator ref z) k.val)
    have encoded (h) (unit : IsUnit h) (inside : keep (h*h.transpose)) (k : Fin 661) : phaseRead owner x (labelSpectator h z) k.val =
        selectedFrame w (Frames.initialRefs k.val) (stored k) := by
      rw [show selectedFrame w (Frames.initialRefs k.val) (stored k) = _ from
        (selectedFrame w (Frames.initialRefs k.val)).apply_symm_apply _]
      funext a
      simpa only [phaseRead,Copy.extendStored,dite_eq_left k.isLt] using
        input (owner k) (Fin.castSucc_ne_last _) h unit inside z a
    have read (h : Cover.LabelPadding.Label 64 w) (unit : IsUnit h) (inside : keep (h*h.transpose)) :=
      act.gramEndpoint z stored h unit (fun h' u eq => encoded h' u (eq ▸ inside)) j
    have same := (read g live kept).trans (read ref unitRef keepRef).symm
    simpa only [phaseRead,Copy.extendStored,dite_eq_left j.isLt] using congrFun same s
  · rw [act.2 i permanent (fun j eq => owned ⟨j,eq⟩)]
    exact input i permanent g live kept z s

/-- Replication is inherited by each successive class run, including when
different invocations use the same permanent tape for helpers. -/
theorem stageTrace_liveReplicatedAt {n : Fin 9} {w B K : ℕ} {x out}
    {keep : Cover.LabelPadding.Label 64 w → Prop} {ref : Cover.LabelPadding.Label 64 w}
    (unitRef : IsUnit ref) (keepRef : keep (ref*ref.transpose))
    (trace : stageRuns.foldr (fun k next a => ∃ b, InvocationEffect n k.1 k.2 w B K a b ∧ next b)
      (fun a => a = out) x) (input : LiveReplicatedAt (B := B) (K := K) keep ref x) :
    LiveReplicatedAt (B := B) (K := K) keep ref out := by
  generalize stageRuns = order at trace
  induction order generalizing x with
  | nil => exact trace ▸ input
  | cons k rest ih =>
    obtain ⟨y,run,tail⟩ := trace
    exact ih (run.liveReplicatedAt unitRef keepRef input) tail

/-- On each permanent tape the active stream at a live label agrees with
the identity-label stream at the same block and spectator. -/
def LiveReplicated {w B K : ℕ}
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) : Prop :=
  ∀ i, i ≠ Fin.last 142080 → ∀ g, IsUnit g →
    ∀ (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (s : Swap.Shear.State (Fin 8) (ZMod (prime^w))),
      x i (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (labelSpectator g z)) =
      x i (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) (labelSpectator 1 z))

theorem InvocationEffect.liveReplicated {n : Fin 9} {r : Fin 32} {d : Fin 5} {w B K : ℕ} {x y}
    (act : InvocationEffect n r d w B K x y) (input : LiveReplicated (w := w) (B := B) (K := K) x) :
    LiveReplicated (w := w) (B := B) (K := K) y :=
  fun i h g u => act.liveReplicatedAt (keep := fun _ => True) isUnit_one trivial
    (fun k hk a ha _ => input k hk a ha) i h g u trivial

theorem stageTrace_liveReplicated {n : Fin 9} {w B K : ℕ} {x out}
    (trace : stageRuns.foldr (fun k next a => ∃ b, InvocationEffect n k.1 k.2 w B K a b ∧ next b)
      (fun a => a = out) x) (input : LiveReplicated (w := w) (B := B) (K := K) x) :
    LiveReplicated (w := w) (B := B) (K := K) out :=
  fun i h g u => stageTrace_liveReplicatedAt (keep := fun _ => True) isUnit_one trivial trace
    (fun k hk a ha _ => input k hk a ha) i h g u trivial

/-- Source and helper reads agree whenever their input label agrees. -/
theorem InvocationEffect.otherRead_congr {n : Fin 9} {r : Fin 32} {d : Fin 5}
    {w B K : ℕ} {x y x' y'} (act : InvocationEffect n r d w B K x y)
    (act' : InvocationEffect n r d w B K x' y') (g)
    (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661)
    (outside : i.val < 111 ∨ 222 ≤ i.val) :
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let j := labelSpectator g z
    phaseRead owner x j = phaseRead owner x' j →
      phaseRead owner y j i.val = phaseRead owner y' j i.val := by
  intro owner j same
  rw [act.otherRead g z i outside,act'.otherRead g z i outside]
  exact congrArg (fun stream => selectedFrame w (Frames.finalRefs i.val)
    ((selectedFrame w (Frames.initialRefs i.val)).symm stream)) (congrFun same i.val)

open IntegerMultBounds.Swap.Modular Matrix in
/-- In its own prefix coordinates the target owner needs only the inverse
basis pass. The decoded stream is read after exchanging the first seven
digits, with the spectator unchanged. -/
theorem InvocationEffect.targetPrefix (t : Fin 111) :
    let k : Fin 636 := ⟨525+t.val,by omega⟩
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w B K,
      0 < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      let volume := (prime^w)^16*W
      let C := reduce (prime^w) (frameBasis k false)
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner volume),
        SharedBankSkeleton.ofStage stage = machine ∧ stage.cost = c*volume ∧
        ∀ n r d x y, InvocationEffect n r d w B K x y → ∀ g z s,
          let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
          let reg : Fin 661 := ⟨111+t.val,by omega⟩
          let before := fun h => labelPhase w (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)
            (phaseRead owner x (labelSpectator h z))
          let stored := FramedCircuit.decode (fun i => selectedFrame w (Frames.scatterFinish Frames.beforeScatter i))
            (labelScatter n before g)
          let output := FramedCircuit.moduleRun ((sectionB ++ sectionC).map RawGate.toCircuit) stored
          stage.transform (y (owner reg)) (FlatCoordinateLayout.index
            (AffineFieldCoordinates.embed s) (labelSpectator g z)) =
            output reg.val (M8.Exchange.transform C C
              (M8.Exchange.exchange (prefixMask (ZMod (prime^w)) 7) s)) := by
  intro k
  obtain ⟨c,machine,run⟩ := frameBasis_owner k true
  refine ⟨c,machine,?_⟩
  intro w B K hW W volume C
  obtain ⟨stage,fixed,cost,reads⟩ := run w W hW
  refine ⟨stage,fixed,cost,?_⟩
  intro n r d x y act g z s owner reg before stored output
  let D := reduce (prime^w) (frameBasis k true)
  let E := prefixMask (ZMod (prime^w)) 7
  let P := reduce (prime^w) (selectedProjector k)
  obtain ⟨_,dc,_,_,conj⟩ := frameBasis_spec k w
  rw [show Geometry.Dimensions.value k.val = 7 from (Nine.target_frames t t.isLt).2.2.1] at conj
  change D*C=1 at dc
  change C*E*D=P at conj
  have pe : P*C=C*E := by rw [← conj,Matrix.mul_assoc (C*E),dc,mul_one]
  have rest : (1-P)*C=C*(1-E) := by rw [Matrix.sub_mul,one_mul,Matrix.mul_sub,mul_one,pe]
  let a := M8.Exchange.transform C C s
  have back : M8.Exchange.transform D D a = s := by
    simp [a,M8.Exchange.transform,mulVec_mulVec,dc]
  have read := reads (y (owner reg)) a (labelSpectator g z)
  change stage.transform _ (FlatCoordinateLayout.index
    (AffineFieldCoordinates.embed (M8.Exchange.transform D D a)) _) = _ at read
  rw [back] at read
  rw [read]
  have finish := congrFun (congrFun (act.finalRead g z) reg.val) a
  change phaseRead owner y (labelSpectator g z) reg.val a =
    selectedFrame w (Frames.snapshot Frames.finalRefs reg.val) (output reg.val) a at finish
  simp only [phaseRead,Copy.extendStored,dite_eq_left reg.isLt,Frames.snapshot,ite_eq_left reg.isLt] at finish
  rw [(Nine.target_frames t.val t.isLt).2.1] at finish
  refine (finish.trans (selectedFrame_rational w k _ _)).trans (congrArg (output reg.val) ?_)
  change M8.Exchange.exchange P a = M8.Exchange.transform C C (M8.Exchange.exchange E s)
  simp only [a,M8.Exchange.exchange,M8.Exchange.transform,mulVec_add,mulVec_mulVec,pe,rest]

open M8.RevMachine in
private theorem targetPort_cost [M8.Machine.Net] {c total w V : ℕ}
    (coeff : c ≤ total) (width : 1 ≤ w) (volume : 1 ≤ V) :
    ((c*V + 2*LeafCore.coreCost V w + 3 : ℕ) : ℝ) ≤
      ((total : ℝ) + 2*|LeafCore.C| + 3) * (w : ℝ)^M8.Machine.BudgetBound.tau * V := by
  let power := (w : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast width : (1 : ℝ) ≤ w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have core := RevBudget.coreCost_le V w (L := power) (by rw [max_eq_right width])
  have scans : (c : ℝ)*V ≤ (total : ℝ)*(power*V) :=
    mul_le_mul (by exact_mod_cast coeff) (le_mul_of_one_le_left (Nat.cast_nonneg V) one)
      (Nat.cast_nonneg V) (Nat.cast_nonneg total)
  have joins : 1 ≤ power*V := one_le_mul_of_one_le_of_one_le one (by exact_mod_cast volume)
  change _ ≤ ((total : ℝ) + 2*|LeafCore.C| + 3)*power*V
  push_cast
  nlinarith only [scans,core,joins]

open IntegerMultBounds.Swap.Modular M8.RevMachine in
/-- Reading a target owner after the port correction recovers the decoded
invocation result at the target projector's exchanged address. The same
program works at every width, for every class and every dirty input. -/
theorem InvocationEffect.targetPort [M8.Machine.Net] :
    ∃ rate : ℝ, ∀ t : Fin 111,
    let k : Fin 636 := ⟨525+t.val,by omega⟩
    let l : Fin 636 := ⟨2+t.val,by omega⟩
    ∃ (c : ℕ) (machine : SharedBankSkeleton.Skeleton 1 prime), ∀ w B K,
      0 < w → 0 < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      let volume := (prime^w)^16*W
      let T := reduce (prime^w) (frameBasis l false) * portPivotSwap (ZMod (prime^w)) *
        reduce (prime^w) (frameBasis k true)
      ∃ stage : SharedBankStage.Stage _ 1 prime (@portOwner volume),
        SharedBankSkeleton.ofStage stage = machine ∧
        stage.cost = c*volume + 2*LeafCore.coreCost volume w + 3 ∧
        (stage.cost : ℝ) ≤ rate * (w : ℝ)^M8.Machine.BudgetBound.tau * volume ∧
        ∀ n r d x y, InvocationEffect n r d w B K x y → ∀ g z s,
          let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
          let reg : Fin 661 := ⟨111+t.val,by omega⟩
          let before := fun h => labelPhase w (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)
            (phaseRead owner x (labelSpectator h z))
          let stored := FramedCircuit.decode (fun i => selectedFrame w (Frames.scatterFinish Frames.beforeScatter i))
            (labelScatter n before g)
          let output := FramedCircuit.moduleRun ((sectionB ++ sectionC).map RawGate.toCircuit) stored
          stage.transform (y (owner reg)) (FlatCoordinateLayout.index
            (AffineFieldCoordinates.embed (M8.Exchange.transform T T s)) (labelSpectator g z)) =
            output reg.val (M8.Exchange.exchange (reduce (prime^w) (selectedProjector k)) s) := by
  let src (t : Fin 111) : Fin 636 := ⟨2+t.val,by omega⟩
  let dst (t : Fin 111) : Fin 636 := ⟨525+t.val,by omega⟩
  choose c machine run using fun t => portChart_owner (dst t) (src t)
  let total := ∑ t, c t
  refine ⟨total + 2*|LeafCore.C| + 3,?_⟩
  intro t k l
  refine ⟨c t,machine t,?_⟩
  intro w B K hw hW W volume T
  obtain ⟨stage,fixed,cost,reads⟩ := run t w W hw hW
  refine ⟨stage,fixed,cost,?_,?_⟩
  · rw [cost]
    exact targetPort_cost (Finset.single_le_sum (fun i _ => Nat.zero_le (c i)) (Finset.mem_univ t))
      hw (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW)
  intro n r d x y act g z s owner reg before stored output
  rw [reads]
  have finish := congrFun (congrFun (act.finalRead g z) reg.val) s
  change phaseRead owner y (labelSpectator g z) reg.val s =
    selectedFrame w (Frames.snapshot Frames.finalRefs reg.val) (output reg.val) s at finish
  simp only [phaseRead,Copy.extendStored,dite_eq_left reg.isLt,Frames.snapshot,ite_eq_left reg.isLt] at finish
  rw [(Nine.target_frames t.val t.isLt).2.1] at finish
  exact finish.trans (selectedFrame_rational w k _ _)

/-- Every spectator position belongs to one matrix label, block and trailing cell. -/
private theorem labelSpectator_surjective {w B K : ℕ} (j : Fin (B*prime^(64*(w*64))*K)) :
    ∃ (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B), labelSpectator g z = j := by
  let tail := finProdFinEquiv.symm j
  let block := finProdFinEquiv.symm tail.1
  have count : prime^(64*(w*64)) = (prime^w)^(64*64) := by
    rw [← pow_mul]
    congr 1
    omega
  let digits := FlatCoordinateLayout.coordinates (block.2.cast count)
  let g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w)) := fun i k => digits (finProdFinEquiv (k,i))
  have label : Cover.LabelAddress.address g = block.2.cast count := by
    unfold Cover.LabelAddress.address
    have eq : M8.AtomOps.refine (Cover.Route.cols g) = digits := by
      funext k
      simp only [g,Cover.Route.cols,M8.AtomOps.refine,Prod.mk.eta,Equiv.apply_symm_apply]
    rw [eq,FlatCoordinateLayout.rank_coordinates]
  let z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B :=
    ⟨⟨0,pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _⟩,⟨0,by simp [copyLabelLayout]⟩,block.1,
      ⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,⟨0,by simp [copyLabelLayout]⟩,⟨0,by simp [copyLabelLayout,ActualAffineScaling.modulus]⟩,tail.2⟩
  refine ⟨g,z,Fin.ext ?_⟩
  have packed := congrArg Fin.val (finProdFinEquiv.apply_symm_apply j)
  have inner := congrArg Fin.val (finProdFinEquiv.apply_symm_apply tail.1)
  change (block.1.val*prime^(64*(w*64))+(Cover.LabelAddress.address g).val)*K+tail.2.val = j.val
  rw [label]
  change (block.1.val*prime^(64*(w*64))+block.2.val)*K+tail.2.val = j.val
  change (finProdFinEquiv block).val = tail.1.val at inner
  change (finProdFinEquiv tail).val = j.val at packed
  simp only [finProdFinEquiv_apply_val] at inner packed
  rw [Nat.mul_comm block.1.val,← Nat.add_comm block.2.val,inner,Nat.mul_comm, Nat.add_comm]
  exact packed

/-- A tape supported on one matrix row already represents its padded row sum. -/
theorem singleLabelBank_of_support {w B K : ℕ} (label : Cover.LabelPadding.Label 64 w)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (owner : Fin 661 ↪ Fin 142081) (i : Fin 661)
    (support : ∀ (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B) g, g ≠ label →
      phaseRead owner x (labelSpectator g z) i.val = 0) :
    x (owner i) = singleLabelBank label (collapseLabelBank x) (owner i) := by
  classical
  funext p
  obtain ⟨⟨s,j⟩,rfl⟩ := copyAddress.symm.surjective p
  obtain ⟨g,z,rfl⟩ := labelSpectator_surjective j
  rw [copyAddress_index,singleLabelBank_read]
  by_cases eq : g = label
  · subst g
    rw [ite_eq_left rfl]
    have h := collapseLabelBank_read x owner z i
    rw [Finset.sum_eq_single label (fun g _ ne => support z g ne) (by simp)] at h
    simpa only [phaseRead,Copy.extendStored,dite_eq_left i.isLt] using congrFun h.symm s
  · rw [ite_eq_right eq]
    simpa only [phaseRead,Copy.extendStored,dite_eq_left i.isLt,Pi.zero_apply] using
      congrFun (support z g eq) s

/-- A tape supported on one matrix row already represents its padded row sum. -/
theorem paddedWord_of_offRow {w B K : ℕ} (label : Cover.LabelPadding.Label 64 w)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) (i : Fin 142081)
    (zero : ∀ (a : Fin ((prime^w)^16)) (z : Cover.LabelEntry.Cell (copyLabelLayout w B K) B)
      (g : Cover.LabelPadding.Label 64 w), (Cover.LabelAddress.address g).val ≠ (Cover.LabelAddress.address label).val →
      x i (finProdFinEquiv (a,labelSpectator g z)) = 0) :
    x i = singleLabelBank label (collapseLabelBank x) i := by
  classical
  let base := Fin.castLEEmb (show 661 ≤ 142081 by decide)
  let owner := base.trans (Equiv.swap (base 0) i).toEmbedding
  have pos : owner 0 = i := by simp [owner,base]
  rw [← pos]
  apply singleLabelBank_of_support label x owner 0
  intro z g ne
  funext s
  simp only [phaseRead,Copy.extendStored,dite_eq_left (0 : Fin 661).isLt,Pi.zero_apply]
  rw [pos]
  apply zero
  intro eq
  apply ne
  apply (physicalLabelRow w).injective
  exact Fin.ext (by simpa only [physicalLabelRow_val] using eq)

/-- Two realizations of a class invocation with the same permanent inputs give
the same permanent outputs, even when their temporary tapes differ. -/
theorem InvocationEffect.agree {n : Fin 9} {r : Fin 32} {d : Fin 5} {w B K : ℕ} {x y x' y'}
    (run : InvocationEffect n r d w B K x y) (run' : InvocationEffect n r d w B K x' y')
    (input : ∀ i, i ≠ Fin.last 142080 → x i = x' i) :
    ∀ i, i ≠ Fin.last 142080 → y i = y' i := by
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
  have reads (j) : phaseRead owner x j = phaseRead owner x' j := by
    unfold phaseRead
    congr 1
    funext k s
    exact congrFun (input (owner k) (Fin.castSucc_ne_last _)) _
  intro i permanent
  by_cases covered : ∃ k, owner k = i
  · obtain ⟨k,rfl⟩ := covered
    funext a
    obtain ⟨⟨s,j⟩,rfl⟩ := copyAddress.symm.surjective a
    obtain ⟨g,z,rfl⟩ := labelSpectator_surjective j
    have left := run.1 g z
    have right := run'.1 g z
    change phaseRead owner y _ = _ at left
    change phaseRead owner y' _ = _ at right
    let endpoint := fun (read : Fin (B*prime^(64*(w*64))*K) → ℕ → AddressStream (ZMod (prime^w))) =>
      labelPhase w (sectionB ++ sectionC) (Frames.scatterFinish Frames.beforeScatter)
        (labelScatter n (fun h => labelPhase w (sectionD ++ sectionA) (Frames.snapshot Frames.initialRefs)
          (read (labelSpectator h z))) g)
    have same := congrArg endpoint (funext reads)
    have eq := congrArg (fun bank => bank k.val s) (left.trans (same.trans right.symm))
    simpa only [copyAddress_index,phaseRead,Copy.extendStored,dite_eq_left k.isLt] using eq
  · have off : ∀ k, owner k ≠ i := fun k eq => covered ⟨k,eq⟩
    exact (run.2 i permanent off).trans ((input i permanent).trans (run'.2 i permanent off).symm)

/-- Reading the permanent tapes after a sequence of invocations agrees with
folding any realization of the same invocation effects. -/
theorem invocationTrace_agree {n : Fin 9} {w B K : ℕ}
    {run : (Fin 32 × Fin 5) → _ → _}
    (valid : ∀ (k : Fin 32 × Fin 5) x, InvocationEffect n k.1 k.2 w B K x (run k x))
    (order : List (Fin 32 × Fin 5)) {x out model}
    (trace : order.foldr (fun k next a => ∃ b, InvocationEffect n k.1 k.2 w B K a b ∧ next b)
      (fun a => a = out) x)
    (input : ∀ i, i ≠ Fin.last 142080 → x i = model i) :
    ∀ i, i ≠ Fin.last 142080 → out i = (order.foldl (fun a k => run k a) model) i := by
  induction order generalizing x model with
  | nil => exact trace ▸ input
  | cons k ks ih =>
    obtain ⟨mid,step,rest⟩ := trace
    exact ih rest (step.agree (valid k model) input)

open M8.RevMachine in
/-- The recurring part of one decoded invocation's bill, after separating
linear-volume work. Only the width of a single port remains. -/
noncomputable def decodedCallCost [M8.Machine.Net] (V w : ℕ) (price : ℕ → ℕ) :=
  222*(LeafCore.coreCost V w+7) + 13 +
    ((Geometry.Moves.phaseValues.filter (· != 0)).map price).sum + 9*price 7

open M8.Machine in
private theorem decodedInvocation_cost [Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (engine : CopyTranspose) :
    ∃ D : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (∀ price : ℕ → ℕ, (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
          phaseChildCost w W p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w W) hs ≤ price 7 →
          stage.cost ≤ D*V + decodedCallCost V w price) ∧
        ∀ x, DecodedInvocationEffect n r d w B K x (stage.transform x) := by
  obtain ⟨C,make⟩ := decodedInvocation_stage n r d engine
  let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
  let scalar := fun gs : List RawGate => (gs.map (fun g => 77*g.sources.length+2)).sum
  let paid := Geometry.Moves.phaseEdges.filter (fun p => Geometry.moveRank p.1 p.2 != 0)
  let moves := (paid.map (fun p => 1303+edgeBasis owner p)).sum
  refine ⟨scalar (sectionD++sectionA)+scalar (sectionB++sectionC)+moves+C,?_⟩
  intro w B K hw hB hK W V hs
  obtain ⟨stage,cost,read⟩ := make w B K hw hB hK
  refine ⟨stage,?_,read⟩
  intro price phaseBound copyBound
  have hp := Shared50ModularControl.prime_prime.pos
  have pos : 0 < V := by dsimp only [V,W]; positivity
  let code := fun (gs : List RawGate) (current : ℕ → ℕ) =>
    FramedCircuit.compile (fun i => selectedFrame w (current i)) (gs.map (Frames.framedGate (selectedFrame w)))
  let left := code (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)
  let right := code (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)
  let calls := fun ps : List (ℕ × ℕ) => (ps.map (phaseEdgeBudget owner w W)).sum
  let a := Frames.edges (sectionD++sectionA) (Frames.snapshot Frames.initialRefs)
  let b := Frames.edges (sectionB++sectionC) (Frames.scatterFinish Frames.beforeScatter)
  have l : (left.map (scalarWork V)).sum + left.length ≤ scalar (sectionD++sectionA)*V := compiled_overhead V pos _ _ _
  have r : (right.map (scalarWork V)).sum + right.length ≤ scalar (sectionB++sectionC)*V := compiled_overhead V pos _ _ _
  have e := phaseEdgeBudget_sum owner w W price pos phaseBound
  change (Geometry.Moves.phaseEdges.map (phaseEdgeBudget owner w W)).sum ≤ moves*V + _ at e
  rw [Geometry.Moves.phaseEdges,List.map_append,List.sum_append] at e
  change calls a + calls b ≤ _ at e
  change stage.cost ≤ (left.map (scalarWork V)).sum + calls a + left.length +
    ((right.map (scalarWork V)).sum + calls b + right.length) + C*V + 9*engine.time (copyChild w W) hs +
    222*(M8.RevMachine.LeafCore.coreCost V w+7) + 13 at cost
  simp only [decodedCallCost,Nat.add_mul]
  omega

open M8.Machine in
/-- All replica/class calls of a stage run in schedule order. Each
intermediate bank is the input of the next decoded invocation. -/
theorem decodedPiece_stage [Net] (n : Fin 9) (engine : CopyTranspose := CopyTranspose.original) :
    ∃ D : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ piece : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (∀ price : ℕ → ℕ, (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
          phaseChildCost w W p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w W) hs ≤ price 7 →
          piece.cost ≤ D*V + 160*decodedCallCost V w price) ∧
        ∀ x, stageRuns.foldr (fun k next a => ∃ b, DecodedInvocationEffect n k.1 k.2 w B K a b ∧ next b)
          (fun a => a = piece.transform x) x := by
  choose coeff build using fun k : Fin 32 × Fin 5 => decodedInvocation_cost n k.1 k.2 engine
  refine ⟨(stageRuns.map coeff).sum + stageRuns.length,?_⟩
  intro w B K hw hB hK W V hs
  choose stage cost effect using fun k => build k w B K hw hB hK
  let compile := fun ks : List (Fin 32 × Fin 5) => SharedBankStage.compile
    (phaseOwners (N := V)) (by decide : 0 < 142081) (ks.map stage)
  refine ⟨compile stageRuns,?_,?_⟩
  · intro price phase copy
    have hp := Shared50ModularControl.prime_prime.pos
    have pos : 0 < V := by dsimp only [V,W]; positivity
    have bound (ks : List (Fin 32 × Fin 5)) : (compile ks).cost ≤
        ((ks.map coeff).sum+ks.length)*V + ks.length*decodedCallCost V w price := by
      induction ks with
      | nil => simp [compile,SharedBankStage.compile_cost]
      | cons k ks ih =>
        have step := cost k price phase copy
        change (stage k).cost ≤ coeff k*V + decodedCallCost V w price at step
        change (stage k).cost + (compile ks).cost + 1 ≤ _
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at ih ⊢
        omega
    exact (bound stageRuns).trans_eq (by rw [stageRuns_length])
  · suffices trace : ∀ (ks : List (Fin 32 × Fin 5)) x, ks.foldr
        (fun k next a => ∃ b, DecodedInvocationEffect n k.1 k.2 w B K a b ∧ next b)
        (fun a => a = (compile ks).transform x) x from trace stageRuns
    intro ks
    induction ks with
    | nil => intro x; rfl
    | cons k ks ih => intro x; exact ⟨_,effect k x,ih ((stage k).transform x)⟩

open M8.Machine in
/-- Execute all 160 replica/class invocations of one stage piece in order.
Each physical join is included in the linear overhead. -/
theorem invocationPiece_stage [Net] (n : Fin 9) (engine : CopyTranspose := CopyTranspose.original) :
    ∃ D : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ piece : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (∀ price : ℕ → ℕ, (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
          phaseChildCost w W p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w W) hs ≤ price 7 →
          piece.cost ≤ D*V + 160*(2*(63*9+252*527)*M8.RevMachine.LeafCore.coreCost V (w*64) +
            ((Geometry.Moves.phaseValues.filter (· != 0)).map price).sum + 9*price 7)) ∧
        ∃ run : (Fin 32 × Fin 5) → (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2), (∀ (k : Fin 32 × Fin 5) x, InvocationEffect n k.1 k.2 w B K x (run k x)) ∧
          ∀ x, piece.transform x = stageRuns.foldl (fun y k => run k y) x := by
  classical
  let spec := fun k : Fin 32 × Fin 5 => (invocation_stage n k.1 k.2 engine).choose_spec
  let coeff := fun k => (spec k).choose
  refine ⟨(stageRuns.map coeff).sum + stageRuns.length,?_⟩
  intro w B K hw hB hK W V hs
  let impl := fun k => (spec k).choose_spec w B K hw hB hK
  let stages := fun k => (impl k).choose
  let compile := fun ks : List (Fin 32 × Fin 5) => SharedBankStage.compile
    (phaseOwners (N := V)) (by decide : 0 < 142081) (ks.map stages)
  refine ⟨compile stageRuns,?_,fun k => (stages k).transform,?_,?_⟩
  · intro price phaseBound copyBound
    let extra := 2*(63*9+252*527)*M8.RevMachine.LeafCore.coreCost V (w*64) +
      ((Geometry.Moves.phaseValues.filter (· != 0)).map price).sum + 9*price 7
    have pos : 0 < V := by
      dsimp only [V,W]
      have := Shared50ModularControl.prime_prime.pos
      positivity
    have bound (ks : List (Fin 32 × Fin 5)) : (compile ks).cost ≤
        ((ks.map coeff).sum + ks.length)*V + ks.length*extra := by
      induction ks with
      | nil => simp [compile,SharedBankStage.compile_cost]
      | cons k ks ih =>
        have bill := (impl k).choose_spec.2.1 price phaseBound copyBound
        change (stages k).cost ≤ coeff k*V + _ + _ + _ at bill
        have localCost : (stages k).cost ≤ coeff k*V+extra := by simpa only [extra,Nat.add_assoc] using bill
        change (stages k).cost + (compile ks).cost + 1 ≤ _
        simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at ih ⊢
        omega
    exact (bound stageRuns).trans_eq (by rw [stageRuns_length])
  · intro k x
    obtain ⟨_,_,endpoint,mid⟩ := (impl k).choose_spec
    refine ⟨endpoint x,?_⟩
    intro i live outside
    obtain ⟨before,after,first,scatter,last⟩ := mid x
    have same := copySchedule_other scatter i live outside
    refine (last.2 i outside).trans (Eq.trans ?_ (first.2 i outside))
    funext t
    exact congrFun same (Fin.cast (copyLabel_volume w B K).symm t)
  · intro x
    dsimp only [compile]
    rw [SharedBankStage.compile_transform]
    simp [SharedBankStage.execute,List.foldl_map]

open M8.Machine in
/-- The stage built from the reference COPY and phase programs. -/
noncomputable def referenceStage [Net] (n : Fin 9) {w B K : ℕ}
    (hw : 0 < w) (hB : 0 < B) (hK : 0 < K) :=
  ((invocationPiece_stage n).choose_spec w B K hw hB hK).choose

open M8.Machine in
theorem stageTrace_transform [Net] (n : Fin 9) {w B K : ℕ}
    (hw : 0 < w) (hB : 0 < B) (hK : 0 < K) {x out}
    (trace : stageRuns.foldr (fun k next a => ∃ b, InvocationEffect n k.1 k.2 w B K a b ∧ next b)
      (fun a => a = out) x) :
    ∀ i, i ≠ Fin.last 142080 → out i = (referenceStage n hw hB hK).transform x i := by
  obtain ⟨run,valid,endpoint⟩ := ((invocationPiece_stage n).choose_spec w B K hw hB hK).choose_spec.2
  unfold referenceStage
  rw [endpoint]
  exact invocationTrace_agree valid stageRuns trace (fun _ _ => rfl)

open M8.Machine in
/-- The nine stage pieces consume exactly the phase and COPY portions of the
node's child inventory. The remainder calls are available to the idle pieces. -/
theorem invocationPieces_nodeCost [Net] (engine : CopyTranspose := CopyTranspose.original) :
    ∃ D : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ pieces : Fin 9 → SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (∀ price : ℕ → ℕ, (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
          phaseChildCost w W p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w W) hs ≤ price 7 →
          (∑ n, (pieces n).cost) + 160*(BitOccurrences.remainders.map price).sum ≤ D*V +
            1440*(2*(63*9+252*527)*M8.RevMachine.LeafCore.coreCost V (w*64)) + (nodeChildren5.map price).sum) ∧
        ∀ n, ∃ run : (Fin 32 × Fin 5) → (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2),
          (∀ (k : Fin 32 × Fin 5) x, InvocationEffect n k.1 k.2 w B K x (run k x)) ∧
          ∀ x, (pieces n).transform x = stageRuns.foldl (fun y k => run k y) x := by
  classical
  choose coeff make using fun n => invocationPiece_stage n engine
  refine ⟨∑ n, coeff n,?_⟩
  intro w B K hw hB hK W V hs
  choose pieces cost action using fun n => make n w B K hw hB hK
  refine ⟨pieces,?_,action⟩
  intro price phaseBound copyBound
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun n _ => cost n price phaseBound copyBound)
  rw [Finset.sum_add_distrib,← Finset.sum_mul] at sum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at sum
  rw [nodeChildren5_split_price]
  rw [show (fun x : ℕ => decide (x ≠ 0)) = (fun x => x != 0) by funext x; cases x <;> rfl]
  dsimp only [V,W]
  omega

open M8.Machine M8.RevMachine in
/-- The nine decoded pieces have the selected child-price sum, plus the
width-w port corrections. Remainder prices are accounted for
separately from execution of the pieces. -/
theorem decodedPieces_nodeCost [Net] (engine : CopyTranspose := CopyTranspose.original) :
    ∃ D : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ pieces : Fin 9 → SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (∀ price : ℕ → ℕ, (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
          phaseChildCost w W p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w W) hs ≤ price 7 →
          (∑ n, (pieces n).cost) + 160*(BitOccurrences.remainders.map price).sum ≤
            D*V + (nodeChildren5.map price).sum +
              1440*(222*(LeafCore.coreCost V w+7) + 13)) ∧
        ∀ n x, stageRuns.foldr (fun k next a => ∃ b, DecodedInvocationEffect n k.1 k.2 w B K a b ∧ next b)
          (fun a => a = (pieces n).transform x) x := by
  classical
  choose coeff make using fun n => decodedPiece_stage n engine
  refine ⟨∑ n, coeff n,?_⟩
  intro w B K hw hB hK W V hs
  choose pieces cost trace using fun n => make n w B K hw hB hK
  refine ⟨pieces,?_,trace⟩
  intro price phase copy
  have sum := Finset.sum_le_sum (s := Finset.univ) (fun n _ => cost n price phase copy)
  rw [Finset.sum_add_distrib,← Finset.sum_mul] at sum
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,decodedCallCost] at sum
  rw [nodeChildren5_split_price]
  rw [show (fun x : ℕ => decide (x ≠ 0)) = (fun x => x != 0) by funext x; cases x <;> rfl]
  dsimp only [V,W]
  omega

open RecursiveInterchangeLayout (Descriptor volume) in
theorem invocationVolume (v : Descriptor) (w B rows : ℕ)
    (width : v.width = 64*w) (split : v.rows = 142080*rows) (label : v.beforeH = B*prime^(64*(w*64))) :
    let K := (prime^w)^112*(v.beforeRows*rows*v.between*v.afterD)
    let W := B*prime^(64*(w*64))*K
    ((prime^w)^16*W)*142080 = volume prime v := by
  intro K W
  have spectators : (prime^w)^112*(v.beforeRows*rows*v.beforeH*v.between*v.afterD) = W := by
    dsimp only [W,K]; rw [label]; ac_rfl
  have size := (copyChild_measures v w rows width split).2
  rwa [spectators,copyChild_volume] at size

open RecursiveInterchangeLayout (Descriptor volume) in
/-- The concrete phase descriptor satisfies both child measures in the
five-class recurrence, including intervals with spectators on both sides. -/
theorem phaseChild_parent_measures (v : Descriptor) (w B rows : ℕ) (p : ℕ × ℕ)
    (checked : Geometry.Moves.CheckedPair p)
    (width : v.width = 64*w) (split : v.rows = 142080*rows) (label : v.beforeH = B*prime^(64*(w*64))) :
    let K := (prime^w)^112*(v.beforeRows*rows*v.between*v.afterD)
    let W := B*prime^(64*(w*64))*K
    let a := Geometry.Dimensions.value p.1
    let b := Geometry.Dimensions.value p.2
    let child := phaseIntervalChild (min a b) (max a b) w W
    child.width*64 = Geometry.moveRank p.1 p.2*v.width ∧ volume prime child*142080 = volume prime v := by
  intro K W a b child
  have bounded (k : ℕ) (h : k < 636) : Geometry.Dimensions.value k ≤ 8 := by
    rw [← Geometry.Dimensions.dimension k h]
    simpa using Submodule.finrank_le (Geometry.label k)
  constructor
  · rw [show child.width = _ from phaseIntervalChild_width checked w W,width]
    ring
  · rw [show volume prime child = _ from phaseIntervalChild_volume (min_le_max : min a b ≤ max a b)
        (max_le (bounded _ checked.1) (bounded _ checked.2.1)) w W]
    exact invocationVolume v w B rows width split label

open RecursiveInterchangeLayout (Descriptor volume) in
open M8.Machine in
/-- Normalize the physical stage costs by the parent volume. Every recursive
occurrence is charged at its own rank with weight 1/142080. -/
theorem invocationPieces_normalized [Net] (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℝ, ∀ (v : Descriptor) (w B rows : ℕ), v.Positive → 0 < w → 0 < B →
      v.width = 64*w → v.rows = 142080*rows → v.beforeH = B*prime^(64*(w*64)) →
      let K := (prime^w)^112*(v.beforeRows*rows*v.between*v.afterD)
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ pieces : Fin 9 → SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (∀ (price : ℕ → ℕ) (rate : ℕ → ℝ),
          (∀ p ∈ Geometry.Moves.phaseEdges, Geometry.moveRank p.1 p.2 ≠ 0 →
            phaseChildCost w W p ≤ price (Geometry.moveRank p.1 p.2)) →
          engine.time (copyChild w W) hs ≤ price 7 →
          (∀ j ∈ nodeChildren5, (price j : ℝ) ≤ V*rate j) →
          ((∑ n, (pieces n).cost) + 160*(BitOccurrences.remainders.map price).sum : ℕ) ≤
            (volume prime v : ℝ)*(C*(w : ℝ)^BudgetBound.tau + (nodeChildren5.map rate).sum/142080)) ∧
        ∀ n, ∃ run : (Fin 32 × Fin 5) → (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2),
          (∀ k x, InvocationEffect n k.1 k.2 w B K x (run k x)) ∧
          ∀ x, (pieces n).transform x = stageRuns.foldl (fun y k => run k y) x := by
  obtain ⟨D,make⟩ := invocationPieces_nodeCost engine
  obtain ⟨C,route⟩ := labelRoute_cost_bound D (1440*(2*(63*9+252*527)))
  refine ⟨C/142080,?_⟩
  intro v w B rows positive hw hB width split label K W V hs
  obtain ⟨before,row,_,mid,after⟩ := positive
  have hr : 0 < rows := by rw [split] at row; omega
  have hp := Shared50ModularControl.prime_prime.pos
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨pieces,time,action⟩ := make w B K hw hB hK
  refine ⟨pieces,?_,action⟩
  intro price rate phaseBound copyBound childBound
  have children (xs : List ℕ) (bound : ∀ j ∈ xs, (price j : ℝ) ≤ V*rate j) :
      ((xs.map price).sum : ℝ) ≤ V*(xs.map rate).sum := by
    induction xs with
    | nil => simp
    | cons j xs ih =>
      simp only [List.map_cons,List.sum_cons,Nat.cast_add,mul_add]
      exact add_le_add (bound j List.mem_cons_self) (ih (fun i hi => bound i (List.mem_cons_of_mem _ hi)))
  have size := invocationVolume v w B rows width split label
  have sizeR : (volume prime v : ℝ) = V*142080 := by exact_mod_cast size.symm
  have bill := time price phaseBound copyBound
  rw [← Nat.mul_assoc 1440 (2*(63*9+252*527))] at bill
  have paid := (Nat.cast_le (α := ℝ)).mpr bill
  conv at paid => rhs; rw [Nat.cast_add]
  exact (paid.trans (add_le_add (route V w hw) (children _ childBound))).trans_eq (by rw [sizeR]; ring)

end IntegerMultBounds.MathlibTM2.M6.BitNode
