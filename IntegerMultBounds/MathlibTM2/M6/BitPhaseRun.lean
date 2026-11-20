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

private theorem phaseLogicalRead (w : ℕ) (gates : List RawGate) (current : ℕ → ℕ)
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
private theorem flatCopyStage {k V : ℕ} {v : Descriptor} (size : volume prime v = V)
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
private theorem compiled_overhead {w : ℕ} (V : ℕ) (positive : 0 < V)
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
private theorem phaseEdgeBudget_sum [Net] {k : ℕ} (owner : Fin 661 ↪ Fin k) (w W : ℕ) (price : ℕ → ℕ)
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

end IntegerMultBounds.MathlibTM2.M6.BitNode
