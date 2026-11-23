module

public import IntegerMultBounds.Networks.Certificates.PR589.GateSources
public import IntegerMultBounds.MathlibTM2.M6.BitCopyRecordSetup
public import IntegerMultBounds.MathlibTM2.M6.BitRouteRun

/-! Physical cover-label reads of the pointwise COPY window. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Cover
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.RevMachine (ext ext_apply)

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Keep the sixteen active fields ahead of the cover label and trailing
spectators. The routing program can use width zero in its payload descriptor. -/
noncomputable def copyLabelLayout (w B K : ℕ) : Descriptor :=
  ⟨(prime^w)^16,1,B*prime^(64*(w*64)),0,1,K⟩

private theorem copyLabel_index {w B K : ℕ} (z : LabelEntry.Cell (copyLabelLayout w B K) B) (before : ℕ) :
    RecursiveInterchangeLayout.index prime (copyLabelLayout w B K) z.a z.row before z.h z.mid z.d z.after =
      z.a.val*(B*prime^(64*(w*64))*K)+(before*K+z.after.val) := by
  have row : z.row.val = 0 := Nat.lt_one_iff.mp z.row.isLt
  have mid : z.mid.val = 0 := Nat.lt_one_iff.mp z.mid.isLt
  have h : z.h.val = 0 := Nat.lt_one_iff.mp (by simpa [copyLabelLayout,ActualAffineScaling.modulus] using z.h.isLt)
  have d : z.d.val = 0 := Nat.lt_one_iff.mp (by simpa [copyLabelLayout,ActualAffineScaling.modulus] using z.d.isLt)
  simp only [RecursiveInterchangeLayout.index,copyLabelLayout,row,mid,h,d,pow_zero,Nat.mul_one,Nat.add_zero]
  exact pack _ _ _ _ _
where
  pack (a V b K k : ℕ) : (a*V+b)*K+k = a*(V*K)+(b*K+k) := by ring

/-- The cover read on this layout is the literal address used by COPY, with
the whole matrix label packed into the spectator index. -/
theorem copyLabel_read {w B K : ℕ} (x : Fin (volume prime (copyLabelLayout w B K)) → ZMod 2)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    let count := prime^(64*(w*64))
    let spectator := (z.b.val*count+(LabelAddress.address g).val)*K+z.after.val
    chartRead x g z = ext x (z.a.val*(B*count*K)+spectator) := by
  intro count spectator
  exact congrArg (ext x) (copyLabel_index z _)

/-- A fanout addition on physical positions induces the same addition on
each cover-label slice when the local move changes the leading field. -/
theorem copyLabel_add {w B K : ℕ}
    (f : Fin ((prime^w)^16) → Fin ((prime^w)^16))
    (src dst out : Fin (volume prime (copyLabelLayout w B K)) → ZMod 2)
    (add : ∀ (a : Fin ((prime^w)^16)) (j : ℕ), j < B*prime^(64*(w*64))*K →
      let W := B*prime^(64*(w*64))*K
      ext out (a.val*W+j) = ext dst (a.val*W+j) + ext src ((f a).val*W+j))
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    chartRead out g z = chartRead dst g z + chartRead src g {z with a := f z.a} := by
  rw [copyLabel_read out,copyLabel_read dst,copyLabel_read src]
  apply add
  apply LabelShift.pack_lt _ z.after.isLt
  apply LabelShift.pack_lt z.b.isLt
  have size : (prime^w)^(64*64) = prime^(64*(w*64)) := by
    rw [← pow_mul]
    congr 1
    omega
  exact size ▸ (LabelAddress.address g).isLt

theorem copyLabel_volume (w B K : ℕ) :
    volume prime (copyLabelLayout w B K) = (prime^w)^16*(B*prime^(64*(w*64))*K) := by
  simp only [volume,copyLabelLayout,pow_zero,Nat.mul_one,Nat.mul_assoc]

/-- Read the exact pointwise target output of the physical COPY window.
The selected modular word changes the active coordinate of the source cell
while its cover label and spectator position stay fixed. -/
theorem copyLabel_window_read {w B K : ℕ} (p : ℕ × ℕ)
    (src dst : Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2)
    (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B) :
    let move := AffineFieldProgram.run (selectedWord w p)
    let output := fun i => dst i + src (copyAddress.symm (move (copyAddress i).1,(copyAddress i).2))
    let view := fun (x : Fin ((prime^w)^16*(B*prime^(64*(w*64))*K)) → ZMod 2) i =>
      x (Fin.cast (copyLabel_volume w B K) i)
    chartRead (view output) g z = chartRead (view dst) g z +
      chartRead (view src) g {z with a := copyActive (move (copyActive.symm z.a))} := by
  intro move output view
  apply copyLabel_add (fun a => copyActive (move (copyActive.symm a)))
  intro a j hj W
  let k : Fin W := ⟨j,hj⟩
  have read (x : Fin ((prime^w)^16*W) → ZMod 2) (b : Fin ((prime^w)^16)) :
      ext (view x) (b.val*W+j) = x (finProdFinEquiv (b,k)) := by
    let i := finProdFinEquiv (b,k)
    have eq : i.val = b.val*W+j := by
      change j+W*b.val = _
      rw [Nat.mul_comm,Nat.add_comm]
    rw [← eq,M8.RevMachine.ext_cast,ext_apply]
  rw [read,read,read]
  have unpack : copyAddress (finProdFinEquiv (a,k)) = (copyActive.symm a,k) := by
    apply copyAddress.symm.injective
    rw [Equiv.symm_apply_apply]
    change finProdFinEquiv (a,k) = finProdFinEquiv (copyActive (copyActive.symm a),k)
    rw [Equiv.apply_symm_apply]
  simp only [output,unpack]
  rfl


/-- The phase header bank precedes the permanent caller tapes. All subsequent
workspaces are private, including the basis passes and recursive transpose. -/
private def PhaseFrame {k t n : ℕ} (bank : Tapes n prime → Tapes k prime → Tapes t prime) : Prop :=
  ∃ slots : Fin k ↪ Fin t, ∀ h x,
    SharedBank.payload (bank h x) slots = x ∧
    SharedBank.strip (bank h x) slots = SharedBank.strip (bank h (SharedBank.empty k prime)) slots

private theorem phaseFrame_append {k t u n : ℕ} {bank : Tapes n prime → Tapes k prime → Tapes t prime}
    (work : Tapes u prime) (frame : PhaseFrame bank) :
    PhaseFrame (fun h x => (bank h x).append work) := by
  obtain ⟨slots,frame⟩ := frame
  refine ⟨⟨fun i => Fin.castAdd u (slots i),(Fin.castAdd_injective _ _).comp slots.injective⟩,?_⟩
  intro h x
  change SharedBank.payload ((bank h x).append work) (fun i => Fin.castAdd u (slots i)) = _ ∧
    SharedBank.strip ((bank h x).append work) (fun i => Fin.castAdd u (slots i)) =
      SharedBank.strip ((bank h _).append work) (fun i => Fin.castAdd u (slots i))
  rw [SharedBankFrames.payload_append_left,SharedBankFrames.strip_append_left,
    SharedBankFrames.strip_append_left,(frame h x).1,(frame h x).2]
  exact ⟨rfl,rfl⟩

private theorem headerOwner_frame {k n : ℕ} : PhaseFrame (fun (h : Tapes n prime) (v : Tapes k prime) => h.append v) := by
  refine ⟨⟨Fin.natAdd n,fun i j eq => Fin.ext (by simpa using congrArg Fin.val eq)⟩,?_⟩
  intro h v
  change SharedBank.payload (h.append v) (Fin.natAdd n) = v ∧ SharedBank.strip (h.append v) (Fin.natAdd n) = SharedBank.strip (h.append (SharedBank.empty k prime)) (Fin.natAdd n)
  constructor
  · apply congrArg₂ Tapes.mk <;> funext i <;> simp [SharedBank.payload,Tapes.append]
  · apply congrArg₂ Tapes.mk <;> funext i <;> induction i using Fin.addCases with
    | left j => simp [SharedBank.strip,Tapes.append]
    | right j => simp [SharedBank.strip,Tapes.append]

open M8.Machine in
theorem intervalPrepared_frame [Net] {k : ℕ} (n : ℕ := 24) :
    ∃ slots : Fin k ↪ Fin _, ∀ (h : Tapes n prime) (v : Tapes k prime),
      SharedBank.payload (ArbitraryWidthOriginalRun.input (h.append v)) slots = v ∧
      SharedBank.strip (ArbitraryWidthOriginalRun.input (h.append v)) slots =
        SharedBank.strip (ArbitraryWidthOriginalRun.input (h.append (SharedBank.empty k prime))) slots := by
  change PhaseFrame _
  unfold ArbitraryWidthOriginalRun.input ArbitraryWidthHighPreparedRun.input
    ArbitraryWidthHighCommonPrepare.input ArbitraryWidthHighBranchPrepare.input ArbitraryWidthHighExecutionInitialize.input
  repeat apply phaseFrame_append
  exact headerOwner_frame

open M8.Machine in
theorem phasePrepared_frame [Net] {k w W : ℕ} (A B : List (FlatCoordinateSchedule.Op 16)) :
    let bank := fun (x : Fin ((prime^w)^16*W) → ZMod 2) (h : Tapes 24 prime) (v : Tapes k prime) =>
      ArbitraryWidthOriginalRun.input (((h.append v).append (basisWorkspace B x)).append (basisWorkspace A x))
    ∃ slots : Fin k ↪ Fin _, ∀ x h v,
      SharedBank.payload (bank x h v) slots = v ∧
      SharedBank.strip (bank x h v) slots = SharedBank.strip (bank 0 h (SharedBank.empty k prime)) slots := by
  intro bank
  suffices frame : PhaseFrame (bank 0) by
    obtain ⟨slots,project⟩ := frame
    refine ⟨slots,fun x h v => ?_⟩
    have same : bank x h v = bank 0 h v := by
      dsimp only [bank]
      rw [basisWorkspace_eq B x 0,basisWorkspace_eq A x 0]
    rw [same]
    exact project h v
  unfold bank ArbitraryWidthOriginalRun.input ArbitraryWidthHighPreparedRun.input
    ArbitraryWidthHighCommonPrepare.input ArbitraryWidthHighBranchPrepare.input ArbitraryWidthHighExecutionInitialize.input
  repeat apply phaseFrame_append
  exact headerOwner_frame

/-- Flat bit streams on permanent owner tapes, with heads at the first cell. -/
noncomputable def phaseOwners {k N : ℕ} (data : Fin k → Fin N → ZMod 2) : Tapes k prime :=
  ⟨fun _ => 0,fun j => putWord (fun _ => blank) 0 (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (data j i))⟩

/-- Execute a list of XOR additions between disjoint sets of permanent tapes. -/
theorem ownerAdds_stage {α β : Type*} {k V : ℕ} (target : α → Fin k) (src : β → Fin k)
    (off : ∀ a b, target a ≠ src b) (entries : List (α × β)) (positive : 0 < V) :
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      stage.tapes = k+2 ∧ (∀ data, stage.output data = stage.input (stage.transform data)) ∧
      stage.cost ≤ 76*entries.length*V ∧ ∀ data j i,
        stage.transform data j i = Circuit.run (SparseCircuit.copies target src entries)
          (fun j => data j i) j := by
  let bs := FlatCoordinateSchedule.bits V
  let controls := CountedLoopReuseAlphabet.controls (a := prime) CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1
  let bank := fun data => (phaseOwners (k := k) (N := V) data).append controls
  let transform := fun (data : Fin k → Fin V → ZMod 2) j i =>
    Circuit.run (SparseCircuit.copies target src entries) (fun j => data j i) j
  let slots := fun i : Fin k => Fin.castAdd 2 (id i)
  have project (data) : SharedBank.payload (bank data) slots = phaseOwners data := by
    rw [show SharedBank.payload (bank data) slots = _ from
      SharedBankFrames.payload_append_left (phaseOwners data) controls id,SharedBankFrames.payload_identity]
  refine ⟨{ tapes := _, states := _, program := SparseRoleCircuit.program target src off entries,
            transform := transform, input := bank, output := fun data => bank (transform data),
            slots := slots, slots_injective := Fin.castAdd_injective ..,
            metadata := (SharedBank.empty k prime).append controls,
            cost := entries.length*(14*V+14*bs.length+34), input_payload := project,
            output_payload := fun data => project _, strip_input := ?_, realizes := ?_ },rfl,fun _ => rfl,?_,?_⟩
  · intro data
    exact (SharedBankFrames.strip_append_left (phaseOwners data) controls id).trans
      (congrArg (fun v : Tapes k prime => v.append controls) (SharedBankFrames.strip_identity _))
  · intro data
    exact SparseRoleCircuit.copies_hoare target src off entries (fun _ _ => blank) (fun _ => 0)
      data bs (FlatCoordinateSchedule.bits_value V)
  · exact SparseRoleCircuit.cost_linear entries.length V bs
      (FlatCoordinateSchedule.bits_value V) (FlatCoordinateSchedule.bits_canonical V) positive
  · intros; rfl

/-- Execute the scalar part of a phase instruction on the same permanent
tapes as its frame changes. All sources are read at their original values. -/
theorem phaseGate_stage {k V : ℕ} (dst : Fin k) (sources : List (Fin k))
    (separate : dst ∉ sources) (positive : 0 < V) :
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      stage.tapes = k+2 ∧ (∀ data, stage.output data = stage.input (stage.transform data)) ∧
      stage.cost ≤ 76*sources.length*V ∧ ∀ data,
        stage.transform data = Function.update data dst
          (fun i => data dst i + (sources.map (fun src => data src i)).sum) := by
  let src := fun j : {j // j ∈ sources} => j.val
  let target := fun _ : Unit => dst
  have off : ∀ a b, target a ≠ src b := fun _ b eq => separate ((show dst = b.val from eq).symm ▸ b.property)
  let entries := sources.attach.map (fun j => ((),j))
  obtain ⟨stage,tapes,restores,bound,effect⟩ := ownerAdds_stage target src off entries positive
  refine ⟨stage,tapes,restores,by simpa [entries] using bound,?_⟩
  intro data
  funext j i
  rw [effect, SparseCircuit.copies_run _ _ _ off]
  by_cases eq : j = dst
  · subst j
    simp [entries,src,target,List.map_map,Function.comp_def]
  · simp [entries,src,target,eq,Ne.symm eq,List.map_map,Function.comp_def]

open IntegerMultBounds.Networks.Certificates.PR589 in
theorem phaseRawGate_stage {k V : ℕ} (owner : Fin 661 ↪ Fin k) (g : RawGate)
    (scheduled : g ∈ program) (positive : 0 < V) :
    let dst := owner ⟨g.target,(register_bounds g scheduled).1⟩
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      stage.tapes = k+2 ∧ (∀ data, stage.output data = stage.input (stage.transform data)) ∧
      stage.cost ≤ 76*g.sources.length*V ∧ ∀ data,
        (∀ j, j ≠ dst → stage.transform data j = data j) ∧
        ∀ j : Fin 661, ∀ i, stage.transform data (owner j) i =
          g.toCircuit.run (Copy.extendStored (fun r => data (owner r) i)) j.val := by
  intro dst
  have separate := target_not_mem_sources g scheduled
  let source := fun j : {j // j ∈ g.sources} =>
    owner ⟨j.val,(register_bounds g scheduled).2 _ j.property⟩
  let sources := g.sources.attach.map source
  have off : dst ∉ sources := by
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    have same : j.val = g.target := congrArg Fin.val (owner.injective eq)
    exact separate (same ▸ j.property)
  obtain ⟨stage,tapes,restores,bill,action⟩ := phaseGate_stage dst sources off positive
  refine ⟨stage,tapes,restores,by simpa [sources] using bill,?_⟩
  intro data
  rw [action]
  refine ⟨fun j h => Function.update_of_ne h ..,?_⟩
  intro j i
  rw [RawGate.run_eq]
  by_cases eq : j.val = g.target
  · have same : owner j = dst := congrArg owner (Fin.ext eq)
    rw [same,Function.update_self,eq,Function.update_self]
    have reads (r : {j // j ∈ g.sources}) : data (source r) i =
        Copy.extendStored (fun a => data (owner a) i) r.val := by
      simp [Copy.extendStored,source,(register_bounds g scheduled).2 _ r.property]
    simp only [sources,List.map_map,Function.comp_def,reads]
    rw [List.attach_map_val (l := g.sources) (f := Copy.extendStored (fun a => data (owner a) i))]
    simp [dst,Copy.extendStored,(register_bounds g scheduled).1]
  · have ne : owner j ≠ dst := fun h => eq (congrArg Fin.val (owner.injective h))
    rw [Function.update_of_ne ne,Function.update_of_ne eq]
    simp [Copy.extendStored,j.isLt]

open IntegerMultBounds.Networks.Certificates.PR589 M8.Machine M8.Machine.Segments SharedPlacementAlphabet in
theorem scheduledPhase_stage [Net] {k : ℕ} (src : Fin k) {p : ℕ × ℕ}
    (checked : Geometry.Moves.CheckedPair p) (paid : 0 < Geometry.moveRank p.1 p.2) :
    ∃ basis : ℕ, ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      let a := Geometry.Dimensions.value p.1
      let b := Geometry.Dimensions.value p.2
      let child := phaseIntervalChild (min a b) (max a b) w W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
        stage.cost = phaseWork basis V (ArbitraryWidthOriginalRun.cost child hs) ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          ∀ s j, stage.transform data src (FlatCoordinateLayout.index (AffineFieldCoordinates.embed
            (AffineFieldProgram.run (selectedWord w p) s)) j) =
            data src (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) := by
  obtain ⟨lt,fits,C,rev,fwd,run⟩ := scheduledPhase_runs checked paid
  let A := description _ rev.good
  let B := description _ fwd.good
  refine ⟨FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant B,?_⟩
  intro w W hw hW V a b child hs
  let result := fun (data : Fin k → Fin V → ZMod 2) =>
    (run src (phaseOwners data) (data src) hw hW rfl rfl).2
  let moved := fun data => (result data).choose
  let transform := fun data => Function.update data src (moved data)
  let bank := fun (x : Fin V → ZMod 2) (h : Tapes 24 prime) (v : Tapes k prime) =>
    ArbitraryWidthOriginalRun.input (((h.append v).append (basisWorkspace B x)).append (basisWorkspace A x))
  let initial := phaseHeaderInput (min a b) (max a b) w W
  let finalBank := phaseHeaderOutput (min a b) (max a b) w W
  obtain ⟨slots,frame⟩ := phasePrepared_frame (k := k) (w := w) (W := W) A B
  have execute (data : Fin k → Fin V → ZMod 2) := (result data).choose_spec.1
  have updated (data : Fin k → Fin V → ZMod 2) :
      setTape (phaseOwners data) src (putWord (fun _ => blank) 0
        (List.ofFn fun i => SparseRoleCircuit.encode (a := prime) (moved data i))) 0 = phaseOwners (transform data) := by
    apply congrArg₂ Tapes.mk <;> funext j <;> by_cases eq : j = src <;> simp [phaseOwners,setTape,transform,eq] <;> rfl
  let machineOf {t q b : ℕ} {g : Program t q prime} {pre post : Tapes t prime → Prop}
      (_ : HoareTime g pre post b) := g
  let machine := machineOf (execute 0)
  refine ⟨{ tapes := _, states := _, program := machine, transform := transform,
            input := fun data => bank (data src) initial (phaseOwners data),
            output := fun data => bank (data src) finalBank (phaseOwners (transform data)),
            slots := slots, slots_injective := slots.injective,
            metadata := SharedBank.strip (bank 0 initial (SharedBank.empty k prime)) slots,
            cost := _, input_payload := fun data => (frame _ _ _).1,
            output_payload := fun data => (frame _ _ _).1,
            strip_input := fun data => (frame _ _ _).2,
            realizes := ?_ },rfl,?_⟩
  · intro data
    have step := execute data
    rw [setTape_append_right,sourceWord_cast] at step
    change HoareTime _ _ (fun z => z = bank (data src) finalBank (setTape (phaseOwners data) src _ 0)) _ at step
    rw [updated data] at step
    exact step
  · intro data
    refine ⟨fun j h => Function.update_of_ne h ..,?_⟩
    intro s j
    change Function.update data src (moved data) src _ = _
    rw [Function.update_self]
    exact (result data).choose_spec.2 s j

open IntegerMultBounds.Networks.Certificates.PR589 M8.Machine in
/-- Read through the selected frame change on just one owner, including the
identity action at rank zero. This is the read direction used by runPhase. -/
theorem phaseEdge_stage [Net] {k : ℕ} (src : Fin k) {p : ℕ × ℕ}
    (checked : Geometry.Moves.CheckedPair p) :
    ∃ basis : ℕ, ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      let a := Geometry.Dimensions.value p.1
      let b := Geometry.Dimensions.value p.2
      let child := phaseIntervalChild (min a b) (max a b) w W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
      ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
        stage.cost = (if Geometry.moveRank p.1 p.2 = 0 then 0 else
          phaseWork basis V (ArbitraryWidthOriginalRun.cost child hs)) ∧
        ∀ data, (∀ j, j ≠ src → stage.transform data j = data j) ∧
          ∀ s j, stage.transform data src (FlatCoordinateLayout.index (AffineFieldCoordinates.embed s) j) =
            data src (FlatCoordinateLayout.index (AffineFieldCoordinates.embed
              (AffineFieldProgram.run (selectedWord w p) s)) j) := by
  classical
  by_cases zero : Geometry.moveRank p.1 p.2 = 0
  · refine ⟨0,?_⟩
    intro w W hw hW V a b child hs
    refine ⟨SharedBankStage.identity _ (Nat.zero_lt_of_lt src.isLt),by simp [zero,SharedBankStage.identity],?_⟩
    intro data
    refine ⟨fun _ _ => rfl,?_⟩
    intro s j
    rw [((modular_scatter w).choose_spec.2.2.1.zero p checked zero)]
    rfl
  · obtain ⟨basis,run⟩ := scheduledPhase_stage src checked (Nat.pos_of_ne_zero zero)
    refine ⟨basis,?_⟩
    intro w W hw hW V a b child hs
    obtain ⟨stage,bill,action⟩ := run w W hw hW
    refine ⟨stage,by simpa [zero] using bill,?_⟩
    intro data
    refine ⟨(action data).1,?_⟩
    intro s j
    have h := (action data).2 (AffineFieldProgram.run (selectedWord w p) s) j
    rw [(modular_scatter w).choose_spec.2.1 p checked s] at h
    exact h

private theorem payload_append {k t u : ℕ} (v : Tapes t prime) (workspace : Tapes u prime)
    (slots : Fin k → Fin (t+u)) (leading : ∀ i, (slots i).val = i.val) (fits : k ≤ t) :
    SharedBank.payload (v.append workspace) slots = SharedBank.payload v (fun i => Fin.castLE fits i) := by
  have same (i) : slots i = Fin.castAdd u (Fin.castLE fits i) := Fin.ext (leading i)
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [same,Tapes.append]

open M8.Machine in
/-- Projecting the leading owner slots of the complete COPY machine discards
all of its private workspaces, for either its initial or its final bank. -/
theorem copyLabel_payload [Net] {t w W : ℕ} (A D : List (FlatCoordinateSchedule.Op 16))
    (owners : Tapes t prime) (controls : Tapes 2 prime) (headers : Tapes 6 prime) (arithmetic : Tapes 15 prime)
    (slots : Fin t → Fin _) (leading : ∀ i, (slots i).val = i.val) :
    SharedBank.payload (copyPrepared (w := w) (W := W) A D (owners.append controls) headers arithmetic) slots = owners := by
  unfold copyPrepared ArbitraryWidthOriginalRun.input ArbitraryWidthHighPreparedRun.input
    ArbitraryWidthHighCommonPrepare.input ArbitraryWidthHighBranchPrepare.input ArbitraryWidthHighExecutionInitialize.input
  rw [payload_append _ _ slots leading (by omega)]
  have peel {k u : ℕ} (v : Tapes k prime) (extra : Tapes u prime) (h : t ≤ k+u) (small : t ≤ k) :
      SharedBank.payload (v.append extra) (fun i => Fin.castLE h i) =
        SharedBank.payload v (fun i => Fin.castLE small i) := payload_append v extra (fun i => Fin.castLE h i) (fun _ => rfl) small
  repeat rw [peel _ _ _ (by omega)]
  cases owners
  rfl

/-- The route block exposes the identical leading owner bank through its
24 public control tapes and its variable private tape count. -/
theorem copyRoute_payload {t : ℕ} (block : M8.RevMachine.Graph.Block (t+24) prime)
    (leading : M8.RevMachine.Blocks.Leading block) (owners : Tapes t prime) (v : Descriptor)
    (d : Fin 22 → Option (List Bool)) :
    SharedBank.payload (SharedBankStageInput.raw (LabelCall.bank owners v d) block.tapes)
        (fun i => block.slots (Fin.castAdd 24 i)) = owners := by
  have all := SharedBankRawCompose.payload_raw (LabelCall.bank owners v d) block.slots leading
  change SharedBank.payload (SharedBank.payload (SharedBankStageInput.raw (LabelCall.bank owners v d) block.tapes) block.slots) (Fin.castAdd 24) = owners
  rw [all]
  cases owners
  apply congrArg₂ Tapes.mk <;> funext i <;> simp [LabelCall.bank,Tapes.append]

private def agreeAfter {t : ℕ} (k : ℕ) (x y : Tapes t prime) : Prop :=
  ∀ i : Fin t, k ≤ i.val → x.head i = y.head i ∧ x.tape i = y.tape i

private theorem agreeOwners {t : ℕ} (x y : Tapes t prime) : agreeAfter t x y :=
  fun i h => False.elim (Nat.not_le_of_lt i.isLt h)

private theorem agreeAppend {k t u : ℕ} {x y : Tapes t prime} (h : agreeAfter k x y)
    (work : Tapes u prime) : agreeAfter k (x.append work) (y.append work) := by
  intro i
  induction i using Fin.addCases with
  | left j => simpa [Tapes.append] using h j
  | right j => simp [Tapes.append]

private theorem strip_eq {t k : ℕ} {x y : Tapes t prime} (h : agreeAfter k x y)
    (slots : Fin k → Fin t) (leading : ∀ i, (slots i).val = i.val) :
    SharedBank.strip x slots = SharedBank.strip y slots := by
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases mem : ∃ j, slots j = i
  all_goals simp only [mem,↓reduceIte]
  all_goals have bound : k ≤ i.val := by
              by_contra! lt
              exact mem ⟨⟨i.val,lt⟩,Fin.ext (leading _)⟩
  · exact (h i bound).1
  · exact (h i bound).2

open M8.Machine in
private theorem copyPrivate [Net] {t w W : ℕ} (A D : List (FlatCoordinateSchedule.Op 16))
    (x y : Tapes t prime) (controls : Tapes 2 prime) (headers : Tapes 6 prime) (arithmetic : Tapes 15 prime)
    (slots : Fin t → Fin _) (leading : ∀ i, (slots i).val = i.val) :
    SharedBank.strip (copyPrepared (w := w) (W := W) A D (x.append controls) headers arithmetic) slots =
    SharedBank.strip (copyPrepared (w := w) (W := W) A D (y.append controls) headers arithmetic) slots := by
  apply strip_eq _ _ leading
  unfold copyPrepared ArbitraryWidthOriginalRun.input ArbitraryWidthHighPreparedRun.input
    ArbitraryWidthHighCommonPrepare.input ArbitraryWidthHighBranchPrepare.input ArbitraryWidthHighExecutionInitialize.input
  repeat apply agreeAppend
  exact agreeOwners x y

theorem routePrivate {t : ℕ} (block : M8.RevMachine.Graph.Block (t+24) prime)
    (leading : M8.RevMachine.Blocks.Leading block) (x y : Tapes t prime) (v : Descriptor)
    (d : Fin 22 → Option (List Bool)) :
    let slots := fun i => block.slots (Fin.castAdd 24 i)
    SharedBank.strip (SharedBankStageInput.raw (LabelCall.bank x v d) block.tapes) slots =
      SharedBank.strip (SharedBankStageInput.raw (LabelCall.bank y v d) block.tapes) slots := by
  intro slots
  apply strip_eq _ _ (fun i => leading (Fin.castAdd 24 i))
  have agree : agreeAfter t (LabelCall.bank x v d) (LabelCall.bank y v d) := agreeAppend (agreeOwners x y) _
  intro i hi
  by_cases small : i.val < t+24
  · simpa only [SharedBankStageInput.raw,dite_eq_left small] using agree ⟨i.val,small⟩ hi
  · simp [SharedBankStageInput.raw,small]

open M8.RevMachine in
/-- Compose both chart routes around a COPY body at their owner tapes. The route
controls and the private tapes of all three machines remain in the postcondition. -/
theorem copyRoute_window_return [M8.Machine.Net] {t w W states : ℕ}
    (route : Graph.Block (t+24) prime) (leading : Blocks.Leading route)
    (v : Descriptor) (d : Fin 22 → Option (List Bool)) (before entered : Tapes t prime)
    (A D : List (FlatCoordinateSchedule.Op 16)) (controls : Tapes 2 prime)
    (headers : Tapes 6 prime) (arithmetic : Tapes 15 prime) (body : Program _ states prime)
    (added out : Tapes t prime) (finalHeaders : Tapes 6 prime) (finalArithmetic : Tapes 15 prime)
    (leave : Graph.Block (t+24) prime) (leaveLeading : Blocks.Leading leave) {r b l : ℕ}
    (entry : GraphContract.Runs route (LabelCall.bank before v d) (LabelCall.bank entered v d) r)
    (run : HoareTime body
      (fun z => z = copyPrepared (w := w) (W := W) A D (entered.append controls) headers arithmetic)
      (fun z => z = copyPrepared (w := w) (W := W) A D (added.append controls) finalHeaders finalArithmetic) b)
    (exitRun : GraphContract.Runs leave (LabelCall.bank added v d) (LabelCall.bank out v d) l) :
    let rs := fun i => route.slots (Fin.castAdd 24 i)
    let cs := fun i : Fin t => Fin.castLE (by omega : t ≤ _) i
    let pair := SharedBankPair.program route.program body rs cs
    let common := SharedBankFrames.commonSlots t route.tapes _
    let ls := fun i => leave.slots (Fin.castAdd 24 i)
    let setup := SharedBankPair.input (SharedBankStageInput.raw (LabelCall.bank before v d) route.tapes)
        (copyPrepared (w := w) (W := W) A D (before.append controls) headers arithmetic) rs cs
    let finish := SharedBankPair.output (SharedBankStageInput.raw (LabelCall.bank before v d) route.tapes)
        (copyPrepared (w := w) (W := W) A D (out.append controls) finalHeaders finalArithmetic) rs cs
    HoareTime (SharedBankPair.program pair leave.program common ls)
      (fun z => z = SharedBankPair.input setup (SharedBankStageInput.raw (LabelCall.bank before v d) leave.tapes) common ls)
      (fun z => z = SharedBankPair.output finish (SharedBankStageInput.raw (LabelCall.bank out v d) leave.tapes) common ls)
      (r+b+1+l+1) := by
  intro rs cs pair common ls setup finish
  have join := SharedBankPair.pair_hoare entry run rs (route.slots_injective.comp (Fin.castAdd_injective t 24)) cs
    (Fin.castLE_injective _) ((copyRoute_payload route leading entered v d).trans
      (copyLabel_payload A D entered controls headers arithmetic cs (fun _ => rfl)).symm)
  have composed := SharedBankPair.pair_hoare join exitRun common (SharedBankFrames.commonSlots_injective ..) ls
    (leave.slots_injective.comp (Fin.castAdd_injective t 24)) (by
      rw [SharedBankPair.output,SharedBankFrames.payload_common]
      exact (copyLabel_payload A D added controls finalHeaders finalArithmetic cs (fun _ => rfl)).trans
        (copyRoute_payload leave leaveLeading added v d).symm)
  let prep := fun (x : Tapes t prime) => copyPrepared (w := w) (W := W) A D (x.append controls)
  let bank := fun (x : Tapes t prime) => LabelCall.bank x v d
  dsimp only [setup,finish,SharedBankPair.input,SharedBankPair.output]
  dsimp only [SharedBankPair.input,SharedBankPair.output] at composed
  rw [copyPrivate (w := w) (W := W) A D entered before controls headers arithmetic cs (fun _ => rfl),
    routePrivate leave leaveLeading added before v d,routePrivate route leading entered before v d,
    copyPrivate (w := w) (W := W) A D added out controls finalHeaders finalArithmetic cs (fun _ => rfl)] at composed
  have same := strip_eq (agreeAppend (agreeAppend (agreeOwners
      (SharedBank.payload (prep added finalHeaders finalArithmetic) cs)
      (SharedBank.payload (prep out finalHeaders finalArithmetic) cs))
      (SharedBank.strip (SharedBankStageInput.raw (bank before) route.tapes) rs))
      (SharedBank.strip (prep out finalHeaders finalArithmetic) cs)) common (fun _ => rfl)
  dsimp only [prep,bank] at same
  rwa [same] at composed

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- The COPY addition in the common chart, before the return route. -/
def CopyFanoutEffect (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) (w B K : ℕ) :
    let N := (prime^w)^16*(B*prime^(64*(w*64))*K)
    (Fin 142081 → Fin N → ZMod 2) → (Fin 142081 → Fin N → ZMod 2) → Prop :=
  fun data out =>
    let io := ownerTape n r d
    let src := io ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    let view := fun x i => x (Fin.cast (copyLabel_volume w B K) i)
    let move := AffineFieldProgram.run (selectedWord w (life.sourceFrame,0))
    out (Fin.last 142080) = 0 ∧ out src = data src ∧
    (∀ k, k ≠ Fin.last 142080 → (∀ j : Fin 661, j.val ∈ life.targets → io j ≠ k) → out k = data k) ∧
    ∀ (j : Fin 661), j.val ∈ life.targets → ∀ (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell (copyLabelLayout w B K) B),
      chartRead (view (out (io j))) g z = chartRead (view (data (io j))) g z +
        chartRead (view (data src)) g {z with a := copyActive (move (copyActive.symm z.a))}

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- The pointwise update made by the host fanout gives the label equation at every target. -/
theorem copyFanout_effect (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) (w B K : ℕ) :
    let W := B*prime^(64*(w*64))*K
    let io := ownerTape n r d
    let src := io ⟨life.source,(Copy.source_bounds life scheduled).2⟩
    let regs := life.targets.attach.map fun j =>
      (⟨j.val,((Copy.target_bounds life scheduled _ j.property).2.trans (by decide : 222 < 661))⟩ : Fin 661)
    let addr := copyAddress (Q := prime^w) (W := W)
    let move := AffineFieldProgram.run (selectedWord w (life.sourceFrame,0))
    ∀ data : Fin 142081 → Fin ((prime^w)^16*W) → ZMod 2,
    let common := fun i => data src (addr.symm (move (addr i).1,(addr i).2))
    CopyFanoutEffect n r d life scheduled w B K data (Function.update
      (fun j i => if j ∈ regs.map io then data j i + common i else data j i) (Fin.last 142080) 0) := by
  intro W io src regs addr move data common
  dsimp only [CopyFanoutEffect]
  have unchanged (k : Fin 142081)
      (outside : ∀ j : Fin 661, j.val ∈ life.targets → io j ≠ k) : k ∉ regs.map io := by
    rintro h
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp h
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hj
    exact outside _ a.property rfl
  refine ⟨Function.update_self ..,?_,?_,?_⟩
  · have off : src ≠ Fin.last 142080 := Fin.castSucc_ne_last _
    have outside (j : Fin 661) (hj : j.val ∈ life.targets) : io j ≠ src := by
      intro eq
      have same := congrArg Fin.val (ownerTape_injective n r d eq)
      have bound := (Copy.target_bounds life scheduled _ hj).2
      have lo := (Copy.source_bounds life scheduled).1
      change j.val = life.source at same
      omega
    have absent := unchanged src outside
    change Function.update (fun j i => if j ∈ regs.map io then data j i + common i else data j i) (Fin.last 142080) 0 src = data src
    simp only [Function.update_of_ne off,ite_eq_right absent]
  · intro k off outside
    have absent := unchanged k outside
    simp only [Function.update_of_ne off,ite_eq_right absent]

  intro j member g z
  have target := List.mem_map_of_mem (f := ownerTape n r d)
    (List.mem_map_of_mem (f := fun k : {k // k ∈ life.targets} =>
      (⟨k.val,((Copy.target_bounds life scheduled _ k.property).2.trans (by decide : 222 < 661))⟩ : Fin 661))
      (List.mem_attach life.targets ⟨j.val,member⟩))
  have off : io j ≠ Fin.last 142080 := Fin.castSucc_ne_last _
  change io j ∈ regs.map io at target
  let added := Function.update (fun j i => if j ∈ regs.map io then data j i + common i else data j i) (Fin.last 142080) 0
  have hit : added (io j) = fun i => data (io j) i + common i := by
    simp only [added,Function.update_of_ne off,ite_eq_left target]
  change chartRead (fun i => added (io j) (Fin.cast (copyLabel_volume w B K) i)) g z = _
  rw [hit]
  exact copyLabel_window_read (life.sourceFrame,0) (data src) (data (io j)) g z

open IntegerMultBounds.Networks.Certificates.PR589 M8.Machine.ArbitraryWidthOriginalRun in
/-- The same width-uniform machine that executes the COPY window realizes its
cover-label addition at every actual target, with the child run charged once. -/
theorem copyLabel_window_runs [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) (engine : CopyTranspose := CopyTranspose.original) :
    ∃ (A D : List (FlatCoordinateSchedule.Op 16)) (states : ℕ) (machine : Program _ states prime),
      ∀ (w B K : ℕ), 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let N := (prime^w)^16*W
      let prepare := copyPrepared (t := 142081+2) (w := w) (W := W) A D
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∀ (data : Fin 142081 → Fin N → ZMod 2) (bs : List Bool), Counter.value bs = N →
      let bank := fun X => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0) (SparseRoleCircuit.encoded X) bs
      ∃ out, HoareTime machine (fun z => z = prepare (bank data) (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W))
        (fun z => z = prepare (bank out) (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W))
        (copyWindowWork (FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant D)
          life.targets.length N bs.length + engine.time (copyChild w W) hs) ∧
        CopyFanoutEffect n r d life scheduled w B K data out := by
  obtain ⟨C,rev,fwd,states,machine,run⟩ := copyWindow_hoare (engine := engine) n r d life scheduled
  refine ⟨_,_,states,machine,?_⟩
  intro w B K hw hB hK W N prepare hs data bs count bank
  have hW : 0 < W := Nat.mul_pos (Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _)) hK
  obtain ⟨exec,_,_⟩ := (run w hw).2.2 hW data bs count
  exact ⟨_,exec,copyFanout_effect n r d life scheduled w B K data⟩

open M8.Machine.ArbitraryWidthOriginalRun in
private theorem commonCopyPrepared_stage [M8.Machine.Net] {k w W V states : ℕ}
    (A D : List (FlatCoordinateSchedule.Op 16)) (bs : List Bool) (hs : Fin 6 → List Bool)
    (machine : Program _ states prime)
    (transform : (Fin k → Fin V → ZMod 2) → Fin k → Fin V → ZMod 2) (cost : ℕ)
    (run : ∀ x,
        let bank := fun (data : Fin k → Fin V → ZMod 2) => PointwiseRoleGate.bank (a := prime) (fun _ _ => blank) (fun _ => 0)
          (SparseRoleCircuit.encoded data) bs
        HoareTime machine (fun z => z = copyPrepared (w := w) (W := W) A D (bank x)
            (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W))
          (fun z => z = copyPrepared (w := w) (W := W) A D (bank (transform x))
            (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W)) cost) :
    ∃ stage : SharedBankStage.Stage _ k prime (phaseOwners (N := V)),
      stage.transform = transform ∧ stage.cost = cost := by
  let controls := CountedLoopReuseAlphabet.controls (a := prime) CountedLoopReuseAlphabet.empty
    (CountedLoopReuseAlphabet.binary bs) 1 1
  let prep := fun x => copyPrepared (w := w) (W := W) A D ((phaseOwners (k := k) (N := V) x).append controls)
  let input := fun x => prep x (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W)
  let output := fun x => prep (transform x) (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W)
  let tapeCount {t q : ℕ} (_ : Program t q prime) := t
  let slots := fun i : Fin k => Fin.castLE (by dsimp [tapeCount]; omega : k ≤ tapeCount machine) i
  exact ⟨{ tapes := _, states := states, program := machine, transform := transform, input := input,
           output := output, slots := slots, slots_injective := Fin.castLE_injective _,
           metadata := SharedBank.strip (input 0) slots, cost := cost, realizes := run,
           input_payload := fun x => copyLabel_payload (w := w) (W := W) A D (phaseOwners x) controls
             (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W) slots (fun _ => rfl),
           output_payload := fun x => copyLabel_payload (w := w) (W := W) A D (phaseOwners (transform x)) controls
             (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W) slots (fun _ => rfl),
           strip_input := fun x => copyPrivate (w := w) (W := W) A D (phaseOwners x) (phaseOwners 0) controls
             (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W) slots (fun _ => rfl) },rfl,rfl⟩

open IntegerMultBounds.Networks.Certificates.PR589 M8.Machine.ArbitraryWidthOriginalRun in
/-- A COPY window on common-coordinate rows is already a permanent-bank
stage. Its only recursive charge is the rank-seven child. -/
theorem commonCopy_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let W := B*prime^(64*(w*64))*K
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        (∀ x, CopyFanoutEffect n r d life scheduled w B K x (stage.transform x)) ∧
        stage.cost ≤ C*V + engine.time (copyChild w W) hs := by
  obtain ⟨A,D,states,machine,runs⟩ := copyLabel_window_runs n r d life scheduled engine
  let basis := FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant D
  refine ⟨504+basis+76*(life.targets.length+2),?_⟩
  intro w B K hw hB hK W V hs
  let bs := FlatCoordinateSchedule.bits V
  choose transform exec effect using fun x => runs w B K hw hB hK x bs (FlatCoordinateSchedule.bits_value V)
  have ready := commonCopyPrepared_stage (w := w) (W := W) (V := V) A D bs hs machine transform
    (copyWindowWork basis life.targets.length V bs.length + engine.time (copyChild w W) hs) exec
  obtain ⟨stage,action,price⟩ := ready
  refine ⟨stage,fun x => action.symm ▸ effect x,?_⟩
  rw [price]
  have hp := Shared50ModularControl.prime_prime.pos
  have pos : 0 < V := by dsimp [V,W]; positivity
  exact Nat.add_le_add_right (copyWindowWork_linear basis life.targets.length pos bs
    (FlatCoordinateSchedule.bits_value V) (FlatCoordinateSchedule.bits_canonical V)) _

open IntegerMultBounds.Networks.Certificates.PR589 M8.Machine.ArbitraryWidthOriginalRun in
/-- Run a COPY directly on an unpadded spectator bank, with one rank-seven
child on that bank's actual volume. -/
theorem compactCopy_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) (engine : CopyTranspose) :
    ∃ C : ℕ, ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      let owner := ownerTape n r d
      let frame := fun j => tapeFrame (copyAddress (Q := prime^w) (W := W)) (selectedFrame w j)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + engine.time (copyChild w W) hs ∧
        ∀ x, let stored := Copy.extendStored fun j => x (owner j)
          (∀ j : Fin 661, stage.transform x (owner j) = Copy.execute frame life stored j) ∧
          (∀ k, k ≠ Fin.last 142080 → (∀ j, owner j ≠ k) → stage.transform x k = x k) := by
  obtain ⟨_,rev,fwd,states,machine,run⟩ := copyWindow_hoare (engine := engine) n r d life scheduled
  let A := M8.Machine.Segments.description _ rev.good
  let D := M8.Machine.Segments.description _ fwd.good
  let basis := FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant D
  refine ⟨504+basis+76*(life.targets.length+2),?_⟩
  intro w W hw hW V hs owner frame
  let bs := FlatCoordinateSchedule.bits V
  let count := FlatCoordinateSchedule.bits_value V
  have window := fun x => (run w hw).2.2 hW x bs count
  obtain ⟨stage,action,price⟩ := commonCopyPrepared_stage (w := w) (W := W) (V := V) A D bs hs machine _
    (copyWindowWork basis life.targets.length V bs.length + engine.time (copyChild w W) hs) (fun x => (window x).1)
  refine ⟨stage,?_,?_⟩
  · rw [price]
    exact Nat.add_le_add_right (copyWindowWork_linear basis life.targets.length (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW) bs
      count (FlatCoordinateSchedule.bits_canonical V)) _
  · intro x stored
    rw [action]
    refine ⟨(window x).2.1,?_⟩
    intro k permanent outside
    dsimp only
    rw [Function.update_of_ne permanent]
    funext i
    split
    · rename_i mem
      obtain ⟨j,_,eqn⟩ := List.mem_map.mp mem
      exact (outside j eqn).elim
    · rfl

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Compose the nine scheduled COPY windows without adding label rows. -/
theorem compactScatter_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose) :
    ∃ C : ℕ, ∀ w W, 0 < w → 0 < W →
      let V := (prime^w)^16*W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      let owner := ownerTape n r d
      let frame := fun j => tapeFrame (copyAddress (Q := prime^w) (W := W)) (selectedFrame w j)
      let read := fun x : Fin 142081 → Fin V → ZMod 2 => Copy.extendStored (x ∘ owner)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
        stage.cost ≤ C*V + 9*engine.time (copyChild w W) hs + 9 ∧
        (∀ x, read (stage.transform x) = Copy.run frame Copy.lifecycles (read x)) ∧
        ∀ x k, k ≠ Fin.last 142080 → (∀ j, owner j ≠ k) → stage.transform x k = x k := by
  let Life := {l // l ∈ Copy.lifecycles}
  let spec := fun l : Life => compactCopy_stage n r d l.val l.property engine
  let coeff := fun l : Life => (spec l).choose
  refine ⟨(Copy.lifecycles.attach.map coeff).sum,?_⟩
  intro w W hw hW V hs owner frame read
  let window := fun l : Life => (spec l).choose_spec w W hw hW
  let stage := fun l : Life => (window l).choose
  let compile := fun ls : List Life => SharedBankStage.compile (phaseOwners (N := V)) (by decide) (ls.map stage)
  let child := engine.time (copyChild w W) hs
  have step (l : Life) (x) : read ((stage l).transform x) = Copy.execute frame l.val (read x) := by
    funext i
    by_cases hi : i < 661
    · change (if h : i < 661 then _ else _) = _
      rw [dite_eq_left hi]
      exact ((window l).choose_spec.2 x).1 ⟨i,hi⟩
    · have miss : i ∉ l.val.targets := fun mem => hi ((Copy.target_bounds _ l.property _ mem).2.trans (by decide))
      have wf := Copy.wellformed _ l.property
      by_cases eq : i = 661
      · subst i; simp [read,Copy.extendStored,Copy.execute]
      · simp [read,Copy.extendStored,hi,Copy.execute,Function.update_of_ne eq,
          Copy.addTargets_eq _ wf.1 wf.2.1,miss]
  have bound (ls : List Life) : (compile ls).cost ≤ (ls.map coeff).sum*V + ls.length*child + ls.length := by
    induction ls with
    | nil => simp [compile,SharedBankStage.compile_cost]
    | cons l ls ih =>
      change (stage l).cost + (compile ls).cost + 1 ≤ _
      have price : (stage l).cost ≤ coeff l*V + child := (window l).choose_spec.1
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [ih,price]
  have effect (ls : List Life) (x) : read ((compile ls).transform x) =
      Copy.run frame (ls.map Subtype.val) (read x) := by
    induction ls generalizing x with
    | nil => rfl
    | cons l ls ih =>
      change read ((compile ls).transform ((stage l).transform x)) = _
      rw [ih,step]
      rfl
  refine ⟨compile Copy.lifecycles.attach,?_,?_,?_⟩
  · have size : Copy.lifecycles.attach.length = 9 := List.length_attach.trans Copy.copy_count
    have cost := bound Copy.lifecycles.attach
    rw [size] at cost
    exact cost
  · intro x
    simpa only [List.attach_map_subtype_val] using effect Copy.lifecycles.attach x
  · intro x k perm outside
    have keep (ls : List Life) (x) : (compile ls).transform x k = x k := by
      induction ls generalizing x with
      | nil => rfl
      | cons l ls ih =>
        exact (ih ((stage l).transform x)).trans (((window l).choose_spec.2 x).2 k perm outside)
    exact keep _ _

open IntegerMultBounds.Networks.Certificates.PR589 in
/-- Observable owner-bank action of one scheduled window, including the
relative source label and preservation of every non-target role. -/
def CopyWindowEffect (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle) (w B K : ℕ)
    (x out : Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2) : Prop :=
    let io := fun j : ℕ => ownerTape n r d (Fin.ofNat 661 j)
    let v := copyLabelLayout w B K
    let move := AffineFieldProgram.run (selectedWord w (life.sourceFrame,0))
    let readSource := fun (z : LabelEntry.Cell v B) => {z with a := copyActive (move (copyActive.symm z.a))}
    out (Fin.last 142080) = 0 ∧
    (∀ k, k ≠ Fin.last 142080 → k ≠ io life.source → k ∉ life.targets.map io → out k = x k) ∧
    (∀ g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w)), chartRead (B := B) (out (io life.source)) g = chartRead (x (io life.source)) g) ∧
    ∀ j ∈ life.targets, ∀ (g : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) (z : LabelEntry.Cell v B),
      chartRead (out (io j)) g z = chartRead (x (io j)) g z +
        chartRead (x (io life.source)) (g*(registerChart w n j).transpose*registerChart w n life.source) (readSource z)

open IntegerMultBounds.Networks.Certificates.PR589 M8.RevMachine in
/-- Transport a common-chart fanout through its entry and return routes. -/
theorem copyWindowEffect_of_routes (n : Fin 9) (r : Fin 32) (d : Fin 5) (life : Copy.Lifecycle)
    (scheduled : life ∈ Copy.lifecycles) (w B K : ℕ) :
    let io := fun j : ℕ => ownerTape n r d (Fin.ofNat 661 j)
    let v := copyLabelLayout w B K
    let W := B*prime^(64*(w*64))*K
    let size := copyLabel_volume w B K
    let view := fun (a : Fin ((prime^w)^16*W) → ZMod 2) (i : Fin (volume prime v)) => a (Fin.cast size i)
    ∀ x entered out : Fin 142081 → Fin (volume prime v) → ZMod 2,
    let data := fun k (i : Fin ((prime^w)^16*W)) => entered k (Fin.cast size.symm i)
    ∀ y, let added := fun k => view (y k)
    let route := fun (enter : Bool) (a b : Fin 142081 → Fin (volume prime v) → ZMod 2) =>
      LabelPermutation.Transport v B w (fun g => g*(if enter then (registerChart w n life.source).transpose else registerChart w n life.source))
        (ext (a (io life.source))) (ext (b (io life.source))) ∧
      (∀ j ∈ life.targets, LabelPermutation.Transport v B w (fun g => g*registerChart w n j)
        (ext (a (io j))) (ext (b (io j)))) ∧
      ∀ k, k ≠ io life.source → k ∉ life.targets.map io → b k = a k
    route true x entered → CopyFanoutEffect n r d life scheduled w B K data y →
    route false added out → CopyWindowEffect n r d life w B K x out := by
  intro io v W size view x entered out data y added route
  rintro ⟨source,targets,untouched⟩ ⟨cleared,retained,others,add⟩ ⟨returned,back,unrouted⟩
  have cancel (k) : view (data k) = entered k := by funext i; simp [view,data]
  dsimp only [CopyWindowEffect]
  let move := AffineFieldProgram.run (selectedWord w (life.sourceFrame,0))
  let readSource := fun (z : LabelEntry.Cell v B) => {z with a := copyActive (move (copyActive.symm z.a))}
  have off (j) : io j ≠ Fin.last 142080 := Fin.castSucc_ne_last _
  have noTmp : Fin.last 142080 ∉ life.targets.map io := by
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    exact off j eq
  have srcEq : Fin.ofNat 661 life.source = ⟨life.source,(Copy.source_bounds life scheduled).2⟩ :=
    Fin.ext (Nat.mod_eq_of_lt (Copy.source_bounds life scheduled).2)
  refine ⟨?_,?_,?_,?_⟩
  · rw [unrouted _ (off _).symm noTmp]
    change view (y _) = 0
    rw [cleared]
    rfl
  · intro k live notSource outside
    rw [unrouted k notSource outside]
    have keep := others k live (by
      intro j hj eq
      apply outside
      apply List.mem_map.mpr
      refine ⟨j.val,hj,?_⟩
      have idx : Fin.ofNat 661 j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
      simpa only [io,idx] using eq)
    change view (y k) = x k
    rw [keep,cancel,untouched k notSource outside]
  · intro g
    let S := registerChart w n life.source
    have enterRead := chartRead_transport source g
    have exitRead := chartRead_transport returned (g*S.transpose)
    change chartRead (out (io life.source)) (g*S.transpose*S) = chartRead (added (io life.source)) (g*S.transpose) at exitRead
    rw [Matrix.mul_assoc,registerChart_inverse w n life.source,Matrix.mul_one] at exitRead
    have saved : added (io life.source) = entered (io life.source) := by
      change view (y (ownerTape n r d (Fin.ofNat 661 life.source))) = _
      rw [srcEq,retained,cancel]
      simp only [io,srcEq]
    rw [exitRead,saved]
    exact enterRead
  · intro j hj g z
    have jBound := ((Copy.target_bounds life scheduled j hj).2.trans (by decide : 222 < 661))
    have jVal : (Fin.ofNat 661 j).val = j := Nat.mod_eq_of_lt jBound
    have action (l : Matrix (Fin 64) (Fin 64) (ZMod (prime^w))) : chartRead (added (io j)) l = chartRead (entered (io j)) l +
        (fun c => chartRead (entered (io life.source)) l (readSource c)) := by
      funext c
      have h := add (Fin.ofNat 661 j) (by rwa [jVal]) l c
      change chartRead (added (io j)) l c = chartRead (view (data (io j))) l c +
        chartRead (view (data (ownerTape n r d ⟨life.source,_⟩))) l (readSource c) at h
      simpa only [cancel,io,srcEq,Pi.add_apply] using h
    apply congrFun (chartRead_copy_add n life.source j _ _ _ _ _ _ source ?_ (back j hj)
      (fun a c => a (readSource c)) action g) z
    intro l
    rw [dataChart_transpose w n (Copy.target_bounds life scheduled j hj).2]
    exact chartRead_transport (targets j hj) l

open IntegerMultBounds.Networks.Certificates.PR589 M8.RevMachine M8.Machine.ArbitraryWidthOriginalRun in
/-- Execute the scheduled charts on both sides of the actual COPY body.
The returned target is read in its original chart, with the retained source
read through the relative chart and the selected local frame change. -/
theorem routedCopy_runs [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) (engine : CopyTranspose := CopyTranspose.original) :
    ∃ (entry leave : Graph.Block (142081+24) prime) (P Q : ℕ)
      (A D : List (FlatCoordinateSchedule.Op 16)) (states : ℕ) (body : Program _ states prime),
      Blocks.Leading entry ∧ Blocks.Leading leave ∧ ∀ (w B K : ℕ), 0 < w → 0 < B → 0 < K →
      let v := copyLabelLayout w B K
      let W := B*prime^(64*(w*64))*K
      let V := volume prime v
      let bank := fun data => LabelCall.bank (copyOwners (v := v) data) v (M8.Stage2Machine.Straight.words (LabelSchedule.base v w))
      let routeCost := fun C => C*V+(63+28*life.targets.length)*LeafCore.coreCost V (w*64)+life.targets.length+1
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∀ (x : Fin 142081 → Fin V → ZMod 2) (bs : List Bool), Counter.value bs = V →
      let controls := CountedLoopReuseAlphabet.controls (a := prime) CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1
      let prep := fun data => copyPrepared (w := w) (W := W) A D ((copyOwners (v := v) data).append controls)
      let rs := fun i => entry.slots (Fin.castAdd 24 i)
      let cs := fun i : Fin 142081 => Fin.castLE (by omega : 142081 ≤ _) i
      let pair := SharedBankPair.program entry.program body rs cs
      let common := SharedBankFrames.commonSlots 142081 entry.tapes _
      let ls := fun i => leave.slots (Fin.castAdd 24 i)
      ∃ out,
        let setup := SharedBankPair.input (SharedBankStageInput.raw (bank x) entry.tapes)
          (prep x (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W)) rs cs
        let finish := SharedBankPair.output (SharedBankStageInput.raw (bank x) entry.tapes)
          (prep out (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W)) rs cs
        HoareTime (SharedBankPair.program pair leave.program common ls)
          (fun z => z = SharedBankPair.input setup (SharedBankStageInput.raw (bank x) leave.tapes) common ls)
          (fun z => z = SharedBankPair.output finish (SharedBankStageInput.raw (bank out) leave.tapes) common ls)
          (routeCost P + (copyWindowWork (FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant D)
            life.targets.length V bs.length + engine.time (copyChild w W) hs) + 1 + routeCost Q + 1) ∧
        CopyWindowEffect n r d life w B K x out := by
  let io := fun j : ℕ => ownerTape n r d (Fin.ofNat 661 j)
  obtain ⟨entry,P,leading,enter⟩ := copyWindow_routes n r d true life scheduled
  obtain ⟨leave,Q,leaveLeading,exitRun⟩ := copyWindow_routes n r d false life scheduled
  obtain ⟨A,D,states,body,run⟩ := copyLabel_window_runs (engine := engine) n r d life scheduled
  refine ⟨entry,leave,P,Q,A,D,states,body,leading,leaveLeading,?_⟩
  intro w B K hw hB hK v W V bank routeCost hs x bs count controls prep rs cs pair common ls
  have pos : v.Positive := ⟨pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _,Nat.zero_lt_one,
    Nat.mul_pos hB (pow_pos Shared50ModularControl.prime_prime.pos _),Nat.zero_lt_one,hK⟩
  obtain ⟨entered,source,targets,untouched,en⟩ := enter v w B hw hB rfl pos x
  let size := copyLabel_volume w B K
  let data := fun k (i : Fin ((prime^w)^16*W)) => entered k (Fin.cast size.symm i)
  let view := fun (a : Fin ((prime^w)^16*W) → ZMod 2) (i : Fin V) => a (Fin.cast size i)
  have cancel (k) : view (data k) = entered k := by funext i; simp [view,data]
  obtain ⟨y,exec,cleared,retained,others,add⟩ := run w B K hw hB hK data bs (count.trans size)
  let added := fun k => view (y k)
  obtain ⟨out,returned,back,unrouted,ex⟩ := exitRun v w B hw hB rfl pos added
  refine ⟨out,?_⟩
  intro setup finish
  constructor
  · dsimp only at exec
    rw [copyOwners_controls size data bs,copyOwners_controls size y bs] at exec
    have eq : (fun k => view (data k)) = entered := funext cancel
    change HoareTime body (fun z => z = prep (fun k => view (data k)) _ _) (fun z => z = prep added _ _) _ at exec
    rw [eq,← size] at exec
    exact copyRoute_window_return entry leading v _ (copyOwners x) (copyOwners entered) A D controls _ _
      body (copyOwners added) (copyOwners out) _ _ leave leaveLeading en exec ex
  · exact copyWindowEffect_of_routes n r d life scheduled w B K x entered out y
      ⟨source,targets,untouched⟩ ⟨cleared,retained,others,add⟩ ⟨returned,back,unrouted⟩

private theorem routedCopy_work (P Q basis targets V core child : ℕ) (pos : 0 < V) :
    let bs := FlatCoordinateSchedule.bits V
    (P*V+(63+28*targets)*core+targets+1) +
      (copyWindowWork basis targets V bs.length + child) + 1 +
      (Q*V+(63+28*targets)*core+targets+1) + 1 ≤
      (P+Q+(504+basis+76*(targets+2))+2*targets+4)*V + 2*(63+28*targets)*core + child := by
  dsimp only
  have localWork := copyWindowWork_linear basis targets pos _ (FlatCoordinateSchedule.bits_value V)
    (FlatCoordinateSchedule.bits_canonical V)
  nlinarith only [localWork, Nat.mul_le_mul_left (2*targets+4) (show 1 ≤ V from pos)]

/-- Both chart routes and local COPY passes fit the label-width allowance;
the recursive transpose contributes exactly its own bill. -/
theorem routedCopy_cost_bound [M8.Machine.Net] (P Q basis targets : ℕ) :
    ∃ C : ℝ, ∀ (V w child : ℕ), 0 < V → 0 < w →
      let core := M8.RevMachine.LeafCore.coreCost V (w*64)
      let route := fun R => R*V+(63+28*targets)*core+targets+1
      let digits := (FlatCoordinateSchedule.bits V).length
      ((route P + (copyWindowWork basis targets V digits + child) + 1 + route Q + 1 : ℕ) : ℝ) ≤
        C*V*(w : ℝ)^M8.Machine.BudgetBound.tau + child := by
  obtain ⟨C, bound⟩ := labelRoute_cost_bound (P+Q+(504+basis+76*(targets+2))+2*targets+4)
    (2*(63+28*targets))
  refine ⟨C, fun V w child pos hw => ?_⟩
  have bill := routedCopy_work P Q basis targets V (M8.RevMachine.LeafCore.coreCost V (w*64)) child pos
  exact (Nat.cast_le.mpr bill).trans (by simpa only [Nat.cast_add] using add_le_add (bound V w hw) (le_refl (child : ℝ)))

private theorem stripPairInput {k t u v a : ℕ}
    (r : Fin k → Fin t) (s : Fin k → Fin u) (l : Fin k → Fin v)
    {x x' : Tapes t a} {y y' : Tapes u a} {z z' : Tapes v a}
    (hx : SharedBank.strip x r = SharedBank.strip x' r)
    (hy : SharedBank.strip y s = SharedBank.strip y' s)
    (hz : SharedBank.strip z l = SharedBank.strip z' l) :
    let slots := SharedBankFrames.commonSlots k t u
    let all := SharedBankFrames.commonSlots k ((k+t)+u) v
    SharedBank.strip (SharedBankPair.input (SharedBankPair.input x y r s) z slots l) all =
      SharedBank.strip (SharedBankPair.input (SharedBankPair.input x' y' r s) z' slots l) all := by
  simp only [SharedBankPair.input, SharedBank.bank, SharedBankFrames.strip_common, hx, hy, hz]

open IntegerMultBounds.Networks.Certificates.PR589 M8.RevMachine M8.Machine.ArbitraryWidthOriginalRun in
/-- A routed window as a composable stage on the permanent owner tapes.
Its initialized private workspace is independent of the incoming data. -/
theorem routedCopy_stage [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (life : Copy.Lifecycle) (scheduled : life ∈ Copy.lifecycles) (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let v := copyLabelLayout w B K
      let V := volume prime v
      let W := B*prime^(64*(w*64))*K
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
        (∀ x, CopyWindowEffect n r d life w B K x (stage.transform x)) ∧
        stage.cost ≤ C*V + 2*(63+28*life.targets.length)*LeafCore.coreCost V (w*64) + engine.time (copyChild w W) hs := by
  obtain ⟨entry,leave,P,Q,A,D,states,body,eLead,lLead,runs⟩ := routedCopy_runs (engine := engine) n r d life scheduled
  let basis := FlatCoordinateCleanSchedule.constant A + FlatCoordinateCleanSchedule.constant D
  refine ⟨P+Q+(504+basis+76*(life.targets.length+2))+2*life.targets.length+4,?_⟩
  intro w B K hw hB hK v V W hs
  let bs := FlatCoordinateSchedule.bits V
  let tapeCount {t q : ℕ} (_ : Program t q prime) := t
  let result := fun x => runs w B K hw hB hK x bs (FlatCoordinateSchedule.bits_value V)
  let transform := fun x => (result x).choose
  have run := fun x => ((result x).choose_spec).1
  let rs := fun i : Fin 142081 => entry.slots (Fin.castAdd 24 i)
  let ls := fun i : Fin 142081 => leave.slots (Fin.castAdd 24 i)
  let cs := fun i : Fin 142081 => Fin.castLE (by dsimp [tapeCount]; omega : 142081 ≤ tapeCount body) i
  let pair := SharedBankPair.program entry.program body rs cs
  let common := SharedBankFrames.commonSlots 142081 entry.tapes (tapeCount body)
  let machine := SharedBankPair.program pair leave.program common ls
  let slots := SharedBankFrames.commonSlots 142081 (tapeCount pair) leave.tapes
  let bank := fun data => LabelCall.bank (copyOwners (T := 142081) (v := v) data) v (M8.Stage2Machine.Straight.words (LabelSchedule.base v w))
  let controls := CountedLoopReuseAlphabet.controls (a := prime) CountedLoopReuseAlphabet.empty (CountedLoopReuseAlphabet.binary bs) 1 1
  let prep := fun data => copyPrepared (w := w) (W := W) A D ((copyOwners (T := 142081) (v := v) data).append controls)
  let input := fun x => SharedBankPair.input
    (SharedBankPair.input (SharedBankStageInput.raw (bank x) entry.tapes)
      (prep x (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W)) rs cs)
    (SharedBankStageInput.raw (bank x) leave.tapes) common ls
  let output := fun x => SharedBankPair.output
    (SharedBankPair.output (SharedBankStageInput.raw (bank x) entry.tapes)
      (prep (transform x) (FixedHeaderBankCopy.headerBank hs) (copyHeaderOutput w W)) rs cs)
    (SharedBankStageInput.raw (bank (transform x)) leave.tapes) common ls
  refine ⟨{ tapes := _, states := _, program := machine, transform := transform, input := input, output := output,
            slots := slots, slots_injective := SharedBankFrames.commonSlots_injective ..,
            metadata := SharedBank.strip (input 0) slots,
            cost := (P*V+(63+28*life.targets.length)*LeafCore.coreCost V (w*64)+life.targets.length+1) +
              (copyWindowWork basis life.targets.length V bs.length + engine.time (copyChild w W) hs) + 1 +
              (Q*V+(63+28*life.targets.length)*LeafCore.coreCost V (w*64)+life.targets.length+1) + 1,
            realizes := fun x => run x,
            input_payload := ?_, output_payload := ?_, strip_input := ?_ },fun x => ((result x).choose_spec).2,?_⟩
  · intro x
    simp only [input,slots,common,tapeCount,pair,SharedBankPair.input,SharedBank.bank,SharedBankFrames.payload_common]
    exact copyRoute_payload entry eLead _ _ _
  · intro x
    simp only [output,slots,tapeCount,pair,SharedBankPair.output,SharedBankFrames.payload_common]
    exact copyRoute_payload leave lLead _ _ _
  · intro x
    exact stripPairInput rs cs ls
      (routePrivate entry eLead (copyOwners x) (copyOwners 0) v _)
      (copyPrivate (w := w) (W := W) A D (copyOwners (v := v) x) (copyOwners (v := v) 0)
        controls (FixedHeaderBankCopy.empty 6) (copyHeaderInput w W) cs (Fin.val_castLE _))
      (routePrivate leave lLead (copyOwners x) (copyOwners 0) v _)
  · have pos : 0 < V := by
      change 0 < volume prime (copyLabelLayout w B K)
      rw [copyLabel_volume]
      have hp := Shared50ModularControl.prime_prime.pos
      positivity
    exact routedCopy_work P Q basis life.targets.length V _ _ pos

open IntegerMultBounds.Networks.Certificates.PR589

/-- The successive owner states satisfy each routed window's chart equations in order. -/
def CopyScheduleEffect (n : Fin 9) (r : Fin 32) (d : Fin 5) (w B K : ℕ) :
    List Copy.Lifecycle → (Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2) →
      (Fin 142081 → Fin (volume prime (copyLabelLayout w B K)) → ZMod 2) → Prop
  | [], x, out => x = out
  | life :: rest, x, out => ∃ y, CopyWindowEffect n r d life w B K x y ∧
      CopyScheduleEffect n r d w B K rest y out

open M8.RevMachine M8.Machine.ArbitraryWidthOriginalRun in
theorem routedCopy_schedule [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℕ, ∀ w B K, 0 < w → 0 < B → 0 < K →
      let v := copyLabelLayout w B K
      let V := volume prime v
      let W := B*prime^(64*(w*64))*K
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values (copyChild w W) i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := v)),
        (∀ x, CopyScheduleEffect n r d w B K Copy.lifecycles x (stage.transform x)) ∧
        stage.cost ≤ C*V + 2*(63*9+28*527)*LeafCore.coreCost V (w*64) + 9*engine.time (copyChild w W) hs + 9 := by
  let Life := {l // l ∈ Copy.lifecycles}
  let spec := fun l : Life => routedCopy_stage (engine := engine) n r d l.val l.property
  let coeff := fun l : Life => (spec l).choose
  refine ⟨(Copy.lifecycles.attach.map coeff).sum, ?_⟩
  intro w B K hw hB hK v V W hs
  let window := fun l : Life => (spec l).choose_spec w B K hw hB hK
  let stage := fun l : Life => (window l).choose
  let compile := fun ls : List Life => SharedBankStage.compile (copyOwners (v := v)) (by decide) (ls.map stage)
  have effect (ls : List Life) : ∀ x, CopyScheduleEffect n r d w B K (ls.map Subtype.val) x ((compile ls).transform x) := by
    induction ls with
    | nil => exact fun _ => rfl
    | cons l ls ih => exact fun x => ⟨_, (window l).choose_spec.1 x, ih ((stage l).transform x)⟩
  let core := LeafCore.coreCost V (w*64)
  let child := engine.time (copyChild w W) hs
  have bound (ls : List Life) : (compile ls).cost ≤ (ls.map coeff).sum*V +
      2*(63*ls.length+28*(ls.map (fun l => l.val.targets.length)).sum)*core + ls.length*child + ls.length := by
    induction ls with
    | nil => simp [compile, SharedBankStage.compile_cost]
    | cons l ls ih =>
      change (stage l).cost + (compile ls).cost + 1 ≤ _
      have localCost : (stage l).cost ≤ coeff l*V + 2*(63+28*l.val.targets.length)*core + child :=
        (window l).choose_spec.2
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [localCost,ih]
  refine ⟨compile Copy.lifecycles.attach, ?_, ?_⟩
  · simpa using effect Copy.lifecycles.attach
  · have specialize (ls : List Life) (count : ls.length = 9)
        (fanout : (ls.map (fun l => l.val.targets.length)).sum = 527) : (compile ls).cost ≤ (ls.map coeff).sum*V + 2*(63*9+28*527)*core + 9*child + 9 := by
          have h := bound ls
          rw [count, fanout] at h
          exact h
    exact specialize Copy.lifecycles.attach (List.length_attach.trans Copy.copy_count)
      ((congrArg List.sum (List.attach_map_val (l := Copy.lifecycles)
        (f := fun l => l.targets.length))).trans Copy.add_count)

open M8.RevMachine M8.Machine.ArbitraryWidthOriginalRun in
/-- On a parent carrying the cover label before its H field, the scheduled COPY
calls have the rank-seven width and one role's volume. All local work is
charged at the label-width exponent, with nine child bills and nine joins. -/
theorem routedCopy_parent [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (engine : CopyTranspose := CopyTranspose.original) :
    ∃ C : ℝ, ∀ (v : Descriptor) (w B rows : ℕ), v.Positive → 0 < w → 0 < B →
      v.width = 64*w → v.rows = 142080*rows → v.beforeH = B*prime^(64*(w*64)) →
      let K := (prime^w)^112 * (v.beforeRows*rows*v.between*v.afterD)
      let W := B*prime^(64*(w*64))*K
      let child := copyChild w W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
      ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := copyLabelLayout w B K)),
        (∀ x, CopyScheduleEffect n r d w B K Copy.lifecycles x (stage.transform x)) ∧
        child.width*64 = 7*v.width ∧ volume prime child*142080 = volume prime v ∧
        (stage.cost : ℝ) ≤ C*volume prime child*(w : ℝ)^M8.Machine.BudgetBound.tau + 9*engine.time child hs + 9 := by
  obtain ⟨P, schedule⟩ := routedCopy_schedule (engine := engine) n r d
  obtain ⟨C, route⟩ := labelRoute_cost_bound P (2*(63*9+28*527))
  refine ⟨C, ?_⟩
  intro v w B rows pos hw hB width splitRows label K W child hs
  obtain ⟨before, rowPos, _, mid, after⟩ := pos
  have hr : 0 < rows := by rw [splitRows] at rowPos; omega
  have hp := Shared50ModularControl.prime_prime.pos
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨stage, effect, bill⟩ := schedule w B K hw hB hK
  have spectators : (prime^w)^112 * (v.beforeRows*rows*v.beforeH*v.between*v.afterD) = W := by
    dsimp only [W,K]
    rw [label]
    ac_rfl
  have measures := copyChild_measures v w rows width splitRows
  dsimp only at measures
  rw [spectators] at measures
  refine ⟨stage, effect, measures.1, measures.2, ?_⟩
  have size : volume prime (copyLabelLayout w B K) = volume prime child :=
    (copyLabel_volume w B K).trans (copyChild_volume w W).symm
  conv at bill => rhs; rw [size]
  have power := route (volume prime child) w hw
  exact (Nat.cast_le.mpr bill).trans (by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      add_le_add (add_le_add power (le_refl ((9 : ℝ)*engine.time child hs))) (le_refl (9 : ℝ)))

open M8.RevMachine M8.Machine.ArbitraryWidthOriginalRun in
/-- Charge each of the nine COPY wrappers to the local routing cost and
retain one recursive child budget per window. -/
theorem routedCopy_recursiveCost [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5) (engine : CopyTranspose)
    (setup swaps : ℕ) :
    ∃ C : ℝ, ∀ (v : Descriptor) (w B rows : ℕ), v.Positive → 0 < w → 0 < B →
      v.width = 64*w → v.rows = 142080*rows → v.beforeH = B*prime^(64*(w*64)) →
      let K := (prime^w)^112 * (v.beforeRows*rows*v.between*v.afterD)
      let W := B*prime^(64*(w*64))*K
      let child := copyChild w W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
      ∀ budget : ℕ, engine.time child hs ≤ budget +
        2*((setup+swaps*Fallback.swapVolumeRate (w-1))*volume prime child) →
      ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := copyLabelLayout w B K)),
        (∀ x, CopyScheduleEffect n r d w B K Copy.lifecycles x (stage.transform x)) ∧
        child.width*64 = 7*v.width ∧ volume prime child*142080 = volume prime v ∧
        (stage.cost : ℝ) ≤ C*volume prime child*(w : ℝ)^M8.Machine.BudgetBound.tau + 9*budget + 9 := by
  obtain ⟨route,run⟩ := routedCopy_parent n r d engine
  obtain ⟨wrap,_,paid⟩ := copyReturn_parentCost setup swaps
  refine ⟨route+9*wrap,?_⟩
  intro v w B rows pos hw hB width splitRows label K W child hs budget engineTime
  obtain ⟨stage,effect,rank,vol,time⟩ := run v w B rows pos hw hB width splitRows label
  refine ⟨stage,effect,rank,vol,time.trans ?_⟩
  have bill := paid (w-1) (volume prime child) budget (engine.time child hs) engineTime
  rw [Nat.sub_add_cancel hw] at bill
  change route*volume prime child*(w : ℝ)^M8.Machine.BudgetBound.tau + 9*engine.time child hs + 9 ≤ _
  linarith only [bill,show (route+9*wrap)*volume prime child*(w : ℝ)^M8.Machine.BudgetBound.tau =
    route*volume prime child*(w : ℝ)^M8.Machine.BudgetBound.tau +
      9*(wrap*volume prime child*(w : ℝ)^M8.Machine.BudgetBound.tau) by ring]

open M8.RevMachine M8.Machine.ArbitraryWidthOriginalRun in
/-- The normalized COPY contribution to the cover recurrence. The matrix entries
are residues modulo prime^w, so their precision is the atom width w.
The nine recursive calls each carry one role's share of the parent volume. -/
theorem routedCopy_normalized [M8.Machine.Net] (n : Fin 9) (r : Fin 32) (d : Fin 5)
    (engine : CopyTranspose) (setup swaps : ℕ) :
    ∃ C : ℝ, ∀ (v : Descriptor) (w B rows : ℕ), v.Positive → 0 < w → 0 < B →
      v.width = 64*w → v.rows = 142080*rows → v.beforeH = B*prime^(64*(w*64)) →
      let K := (prime^w)^112 * (v.beforeRows*rows*v.between*v.afterD)
      let W := B*prime^(64*(w*64))*K
      let child := copyChild w W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
      ∀ (budget : ℕ) (childRate : ℝ), (budget : ℝ) ≤ childRate*volume prime child →
        engine.time child hs ≤ budget+2+(setup+swaps*Fallback.swapVolumeRate (w-1))*volume prime child →
        ∃ stage : SharedBankStage.Stage _ 142081 prime (copyOwners (v := copyLabelLayout w B K)),
          (∀ x, CopyScheduleEffect n r d w B K Copy.lifecycles x (stage.transform x)) ∧
          (stage.cost : ℝ) ≤ volume prime v *
            (C*(w : ℝ)^M8.Machine.BudgetBound.tau + (9/142080)*childRate) := by
  obtain ⟨c,run⟩ := routedCopy_recursiveCost n r d engine setup swaps
  refine ⟨(c+27) / 142080,?_⟩
  intro v w B rows pos hw hB width splitRows label K W child hs budget childRate childTime engineTime
  obtain ⟨stage,effect,_,size,time⟩ := run v w B rows pos hw hB width splitRows label budget.succ.succ
    (engineTime.trans (by change budget+2+_ ≤ budget+2+2*((setup+swaps*Fallback.swapVolumeRate (w-1))*volume prime child); omega))
  refine ⟨stage,effect,time.trans ?_⟩
  have sizeR : (volume prime v : ℝ) = volume prime child * 142080 := by exact_mod_cast size.symm
  obtain ⟨before,row,_,mid,after⟩ := pos
  have hr : 0 < rows := by rw [splitRows] at row; omega
  have hp := Shared50ModularControl.prime_prime.pos
  have V : 0 < volume prime child := by
    change 0 < volume prime (copyChild w W)
    rw [copyChild_volume]
    dsimp only [W,K]; positivity
  let power := (w : ℝ)^M8.Machine.BudgetBound.tau
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast hw) M8.Machine.BudgetBound.exponent_range.1.le
  have room : 1 ≤ (volume prime child : ℝ)*power :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast V) one
  change c*volume prime child*power+9*(budget.succ.succ : ℝ)+9 ≤ _
  push_cast
  rw [sizeR]
  change _ ≤ volume prime child * 142080 * ((c+27)/142080 * power + 9/142080*childRate)
  nlinarith only [room,childTime]

open M8.RevMachine M8.Machine.ArbitraryWidthOriginalRun in
/-- Sum the physical COPY windows over all stages, replicas and host classes. -/
theorem routedCopy_nodeCost [M8.Machine.Net]
    (engine : CopyTranspose) (setup swaps : ℕ) :
    ∃ C : ℝ, ∀ (v : Descriptor) (w B rows : ℕ), v.Positive → 0 < w → 0 < B →
      v.width = 64*w → v.rows = 142080*rows → v.beforeH = B*prime^(64*(w*64)) →
      let K := (prime^w)^112 * (v.beforeRows*rows*v.between*v.afterD)
      let W := B*prime^(64*(w*64))*K
      let child := copyChild w W
      let hs := fun i => FlatCoordinateSchedule.bits (RecursiveDimensionBank.values child i)
      ∀ (budget : ℕ) (childRate : ℝ), (budget : ℝ) ≤ childRate*volume prime child →
        engine.time child hs ≤ budget+2+(setup+swaps*Fallback.swapVolumeRate (w-1))*volume prime child →
        ∃ stages : (Fin 9 × Fin 32 × Fin 5) → SharedBankStage.Stage _ 142081 prime (copyOwners (v := copyLabelLayout w B K)),
          (∀ i x, CopyScheduleEffect i.1 i.2.1 i.2.2 w B K Copy.lifecycles x ((stages i).transform x)) ∧
          (∑ i, ((stages i).cost : ℝ)) ≤ volume prime v *
            (C*(w : ℝ)^M8.Machine.BudgetBound.tau + (12960/142080)*childRate) := by
  classical
  choose rate run using fun i : Fin 9 × Fin 32 × Fin 5 =>
    routedCopy_normalized i.1 i.2.1 i.2.2 engine setup swaps
  refine ⟨∑ i, rate i,?_⟩
  intro v w B rows pos hw hB width splitRows label K W child hs budget childRate childTime engineTime
  choose stages effect time using fun i => run i v w B rows pos hw hB width splitRows label budget childRate childTime engineTime
  refine ⟨stages,effect,(Finset.sum_le_sum (fun i _ => time i)).trans_eq ?_⟩
  rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_mul]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
