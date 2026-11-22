module

public import IntegerMultBounds.MathlibTM2.M6.BitPhaseRun

/-! Read each borrowed label independently across the physical COPY schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Certificates.PR589
open Cover M8.RevMachine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨pow_ne_zero _ Shared50ModularControl.prime_prime.ne_zero⟩
open RecursiveInterchangeLayout (volume)

noncomputable def borrowedRead {w B K : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B)
    (data : Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2) :
    ℕ → AddressStream (ZMod (prime^w)) :=
  Copy.extendStored fun i s => chartRead (data (ownerTape n r d i)) g {z with a := copyActive s}

/-- Routing every register into its scatter chart and back executes the
literal scatter separately at every label, for arbitrary dirty input. -/
theorem borrowedScatter_read {w B K : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    {x entered scattered y : Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2}
    (entry : ∀ i : Fin 661, LabelPermutation.Transport (copyLabelLayout w B K) B w
      (fun g => g*registerChart w n i.val) (ext (x (ownerTape n r d i))) (ext (entered (ownerTape n r d i))))
    (effect : CopyScheduleEffect n r d w B K Copy.lifecycles entered scattered)
    (exitRoute : ∀ i : Fin 661, LabelPermutation.Transport (copyLabelLayout w B K) B w
      (fun g => g*(registerChart w n i.val).transpose) (ext (scattered (ownerTape n r d i))) (ext (y (ownerTape n r d i))))
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B) (i : Fin 661) :
    let frame := fun j => selectedFrame w (Frames.beforeScatter j)
    borrowedRead n r d g z y i.val = frame i.val (FramedCircuit.moduleRun
      (sectionscatter.map RawGate.toCircuit) (FramedCircuit.decode frame (borrowedRead n r d g z x)) i.val) := by
  have input : scatterRead n r d g z entered = borrowedRead n r d g z x := by
    apply congrArg Copy.extendStored
    funext j s
    exact congrFun (chartRead_transport (entry j) g) _
  have output := chartRead_transport (exitRoute i) (g*registerChart w n i.val)
  rw [Matrix.mul_assoc,mul_eq_one_comm.mp (registerChart_inverse w n i.val),Matrix.mul_one] at output
  have read := scatterRead_endpoint effect g z i
  dsimp only at read ⊢
  rw [input] at read
  refine Eq.trans ?_ read
  funext s
  simpa only [borrowedRead,scatterRead,Copy.extendStored,dite_eq_left i.isLt] using
    congrFun output {z with a := copyActive s}

/-- Move the entire live register bank into or out of its scatter charts.
The same block serves every atom width and every batch size. -/
theorem borrowedRoute_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (enter : Bool) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
    let v := copyLabelLayout w B K
    let V := volume prime v
    ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
      stage.cost ≤ C*V + 661*(252*LeafCore.coreCost V (w*64)+1) ∧
      (∀ x (i : Fin 661), let A := registerChart w n i.val
        LabelPermutation.Transport v B w (fun g => g*(if enter then A.transpose else A))
          (ext (x (ownerTape n r d i))) (ext (stage.transform x (ownerTape n r d i)))) ∧
      ∀ x k, (∀ i, ownerTape n r d i ≠ k) → stage.transform x k = x k := by
  let io := (⟨ownerTape n r d,ownerTape_injective n r d⟩ : Fin 661 ↪ Fin 142081)
  obtain ⟨block,C,leading,runs⟩ := ownerChartRoutes io n enter (List.finRange 661) (List.nodup_finRange _)
  refine ⟨C,?_⟩
  intro w B K hw hb hk v V
  have hp := Shared50ModularControl.prime_prime.pos
  have positive : v.Positive := by
    dsimp [v,copyLabelLayout,RecursiveInterchangeLayout.Descriptor.Positive]
    exact ⟨by positivity,by decide,by positivity,by decide,hk⟩
  let result := runs v w B hw hb rfl positive
  let bank := fun x => SharedBankStageInput.raw
    (LabelCall.bank (copyOwners (T := 142081) (v := v) x) v (M8.Stage2Machine.Straight.words (LabelSchedule.base v w))) block.tapes
  let slots := fun i : Fin 142081 => block.slots (Fin.castAdd 24 i)
  refine ⟨{ tapes := _, states := _, program := block.program, transform := fun x => (result x).choose,
            input := bank, output := fun x => bank (result x).choose, slots := slots,
            slots_injective := block.slots_injective.comp (Fin.castAdd_injective _ _),
            metadata := SharedBank.strip (bank 0) slots, cost := C*V+661*(252*LeafCore.coreCost V (w*64)+1),
            input_payload := fun _ => copyRoute_payload block leading _ _ _,
            output_payload := fun _ => copyRoute_payload block leading _ _ _,
            strip_input := fun _ => routePrivate block leading _ _ _ _,
            realizes := fun x => by simpa only [List.length_finRange] using (result x).choose_spec.2.2 },
          le_rfl,fun x i => (result x).choose_spec.1 i (List.mem_finRange _),?_⟩
  intro x k off
  exact (result x).choose_spec.2.1 k (by
    rintro h
    obtain ⟨i,_,eqn⟩ := List.mem_map.mp h
    exact off i eqn)

/-- One charged stage executes all COPY windows on independent borrowed rows. -/
theorem borrowedScatter_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
    let v := copyLabelLayout w B K
    let V := volume prime v
    let W := B*prime^(64*(w*64))*K
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
    ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
      stage.cost ≤ C*V + (2*(63*9+252*527)+1322*252)*LeafCore.coreCost V (w*64) +
        9*engine.time (copyChild w W) hs + 1333 ∧
      (∀ x g z (i : Fin 661), let frame := fun j => selectedFrame w (Frames.beforeScatter j)
        borrowedRead n r d g z (stage.transform x) i.val = frame i.val (FramedCircuit.moduleRun
          (sectionscatter.map RawGate.toCircuit) (FramedCircuit.decode frame (borrowedRead n r d g z x)) i.val)) ∧
      ∀ x k, k ≠ Fin.last 142080 → (∀ i, ownerTape n r d i ≠ k) → stage.transform x k = x k := by
  obtain ⟨C,entry⟩ := borrowedRoute_stage n r d false
  obtain ⟨D,scatter⟩ := routedCopy_schedule n r d engine
  obtain ⟨F,back⟩ := borrowedRoute_stage n r d true
  refine ⟨C+D+F,?_⟩
  intro w B K hw hb hk v V W hs
  obtain ⟨a,ac,enters,aOff⟩ := entry w B K hw hb hk
  obtain ⟨b,acts,bc⟩ := scatter w B K hw hb hk
  obtain ⟨f,fc,leaves,fOff⟩ := back w B K hw hb hk
  refine ⟨SharedBankStage.compose (SharedBankStage.compose a b) f,?_,?_,?_⟩
  · change a.cost+b.cost+1+f.cost+1 ≤ _
    apply (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add ac bc) 1) fc) 1).trans
    dsimp only [V,W,hs,v]
    exact Nat.le_of_eq (by ring)
  · intro x g z i
    exact borrowedScatter_read n r d (enters x) (acts _) (leaves _) g z i
  · intro x k live off
    exact (fOff _ _ off).trans ((copySchedule_other (acts _) k live off).trans (aOff _ _ off))

/-- The copy descriptor and the flat scalar machine read the same register
at each matrix label, including the zero extension above the live bank. -/
theorem borrowedRead_flat {w B K : ℕ} (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (x : Fin 142081 → Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (g : LabelPadding.Label 64 w) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    borrowedRead n r d g z (fun k i => x k (Fin.cast (copyLabel_volume w B K) i)) =
      phaseRead ⟨ownerTape n r d,ownerTape_injective n r d⟩ x (labelSpectator g z) := by
  funext j
  by_cases h : j < 661
  · let i : Fin 661 := ⟨j,h⟩
    funext s
    change borrowedRead n r d g z _ i.val s = _
    simp only [borrowedRead,Copy.extendStored,dite_eq_left i.isLt]
    convert phaseRead_active (⟨ownerTape n r d,ownerTape_injective n r d⟩ : Fin 661 ↪ Fin 142081) i x g z s using 1
  · simp [borrowedRead,phaseRead,Copy.extendStored,h]

noncomputable def borrowedScatter (w : ℕ) (x : ℕ → AddressStream (ZMod (prime^w))) :=
  let frame := fun j => selectedFrame w (Frames.beforeScatter j)
  Copy.extendStored fun i => frame i.val (FramedCircuit.moduleRun (sectionscatter.map RawGate.toCircuit)
    (FramedCircuit.decode frame x) i.val)

theorem borrowedScatter_flat [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*W
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
    ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      stage.cost ≤ C*V + (2*(63*9+252*527)+1322*252)*LeafCore.coreCost V (w*64) +
        9*engine.time (copyChild w W) hs + 1333 ∧
      (∀ x g z, let j := labelSpectator g z
        phaseRead owner (stage.transform x) j = borrowedScatter w (phaseRead owner x j)) ∧
      ∀ x k, k ≠ Fin.last 142080 → (∀ i, owner i ≠ k) → stage.transform x k = x k := by
  obtain ⟨C,build⟩ := borrowedScatter_stage n r d engine
  refine ⟨C,?_⟩
  intro w B K hw hb hk W V owner hs
  obtain ⟨stage,paid,run,off⟩ := build w B K hw hb hk
  let size := copyLabel_volume w B K
  let effect := fun (x y : Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2) =>
    (∀ g z, borrowedRead (B := B) (K := K) n r d g z y = borrowedScatter w (borrowedRead n r d g z x)) ∧
    ∀ k, k ≠ Fin.last 142080 → (∀ i, owner i ≠ k) → y k = x k
  have acts x : effect x (stage.transform x) := by
    refine ⟨?_,off x⟩
    intro g z
    funext j
    by_cases hj : j < 661
    · simpa only [borrowedScatter,Copy.extendStored,dite_eq_left hj] using run x g z ⟨j,hj⟩
    · simp [borrowedRead,borrowedScatter,Copy.extendStored,hj]
  obtain ⟨flat,cost,read⟩ := flatCopyStage size effect _ stage acts paid
  refine ⟨flat,by rwa [copyLabel_volume] at cost,?_,?_⟩
  · intro x g z
    simpa only [borrowedRead_flat] using (read x).1 g z
  · intro x k live outside
    funext i
    exact congrFun ((read x).2 k live outside) (Fin.cast size.symm i)

/-- Execute both scalar phases and COPY on each independent borrowed row. -/
theorem borrowedInvocation_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
    let W := B*prime^(64*(w*64))*K
    let V := (prime^w)^16*W
    let owner : Fin 661 ↪ Fin 142081 := ⟨ownerTape n r d,ownerTape_injective n r d⟩
    let gates := fun done : Bool => if done then sectionB++sectionC else sectionD++sectionA
    let current := fun done : Bool => if done then Frames.scatterFinish Frames.beforeScatter else Frames.snapshot Frames.initialRefs
    let frame := selectedFrame w
    let instr := fun done => FramedCircuit.compile (fun i => frame (current done i)) ((gates done).map (Frames.framedGate frame))
    let phaseCost := fun done => ((instr done).map (scalarWork V)).sum +
      ((Frames.edges (gates done) (current done)).map (phaseEdgeBudget owner w W)).sum + (instr done).length
    let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
    ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      stage.cost ≤ phaseCost false + (C*V + (2*(63*9+252*527)+1322*252)*LeafCore.coreCost V (w*64) +
        9*engine.time (copyChild w W) hs + 1333) + phaseCost true + 2 ∧
      (∀ x g z, let j := labelSpectator g z
        phaseRead owner (stage.transform x) j = labelPhase w (gates true) (current true)
          (borrowedScatter w (labelPhase w (gates false) (current false) (phaseRead owner x j)))) ∧
      ∀ x k, k ≠ Fin.last 142080 → (∀ i, owner i ≠ k) → stage.transform x k = x k := by
  obtain ⟨C,scatter⟩ := borrowedScatter_flat n r d engine
  refine ⟨C,?_⟩
  intro w B K hw hb hk W V owner gates current frame instr phaseCost hs
  have positive : 0 < W := Nat.mul_pos (Nat.mul_pos hb (pow_pos Shared50ModularControl.prime_prime.pos _)) hk
  obtain ⟨a,ac,first,aOff⟩ := invocationPhase_stage owner hw positive false
  obtain ⟨b,bc,middle,bOff⟩ := scatter w B K hw hb hk
  obtain ⟨f,fc,last,fOff⟩ := invocationPhase_stage owner hw positive true
  have checked := Geometry.Moves.phase_checked
  rw [Geometry.Moves.phaseEdges,List.forall_mem_append] at checked
  refine ⟨SharedBankStage.compose (SharedBankStage.compose a b) f,?_,?_,?_⟩
  · change a.cost+b.cost+1+f.cost+1 ≤ _
    change a.cost ≤ phaseCost false at ac
    change f.cost ≤ phaseCost true at fc
    change b.cost ≤ C*V + (2*(63*9+252*527)+1322*252)*LeafCore.coreCost V (w*64) + 9*engine.time (copyChild w W) hs + 1333 at bc
    omega
  · intro x g z j
    change phaseRead owner (f.transform (b.transform (a.transform x))) j = _
    rw [(last _ j).trans (phaseLogicalRead w _ _ checked.2 _)]
    change labelPhase w (gates true) (current true) _ = _
    rw [middle _ g z,(first x j).trans (phaseLogicalRead w _ _ checked.1 _)]
    rfl
  · intro x k live off
    exact (fOff _ _ off).trans ((bOff _ _ live off).trans (aOff _ _ off))

end IntegerMultBounds.MathlibTM2.M6.BitNode
