module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryCall

/-! Execute the stopped directory transpose on six descriptor tapes and a shared payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)

noncomputable def directoryLeafStates [M8.Machine.Net] :=
  (fun {q : ℕ} (_ : Program LeafCore.small q prime) => q) LeafCore.stage1

theorem directoryLeafFits [M8.Machine.Net] : directoryLeafStates ≤ columnCapacity := by
  exact columnLeafFits (0 : Fin 1)

/-- Run the fixed leaf program on the batch descriptor itself. Its workspace
is separate from the archived directory, selectors and owner shadow. -/
theorem directoryLeaf_exec [M8.Machine.Net] {Q : ℕ} {P U : Type}
    (capacity : directoryLeafStates ≤ Q) (body : P → Pr P LeafCore.small Q prime U)
    (batch : Descriptor) (positive : batch.Positive) (word : Fin (volume prime batch) → ZMod 2)
    (u : HS LeafCore.small Q prime U) (S : Stacks LeafCore.small prime) :
    let slot := Fin.castLEEmb LeafCore.seven_le
    let owner := slot (Fin.last 6)
    (∀ j : Fin 6, ∀ k, RadixZeroFill.encodedBinary (Routines.hdr batch j) k =
      readAt blank (S.L (slot j.castSucc)) (S.R (slot j.castSucc)) (k-1)) →
    RecordPayload owner (fun _ => blank) 0 word S →
    (∀ j : Fin LeafCore.small, 7 ≤ j.val → S.L j = [] ∧ S.R j = []) →
    let cost := LeafCore.coreCost (volume prime batch) batch.width
    ∃ z F n, z.user = u.user ∧ n ≤ cost*(LeafCore.small+5)+6 ∧
      Exec body (foreign (liftQ LeafCore.stage1 capacity)) (mk u S) n (mk z F) ∧
      RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) word) F ∧
      ∀ j, (F.L j).length+(F.R j).length ≤ (S.L j).length+(S.R j).length+2*cost := by
  intro slot owner headers payload free cost
  let caller : Tapes 7 prime := ⟨Fin.lastCases 0 (fun _ => 1),
    Fin.lastCases (sourceWord word) (fun j => RadixZeroFill.encodedBinary (Routines.hdr batch j))⟩
  have read (i : Fin 7) (k : ℤ) : caller.tape i k =
      readAt blank (S.L (slot i)) (S.R (slot i)) (k-caller.head i) := by
    induction i using Fin.lastCases with
    | last =>
      simp only [caller,Fin.lastCases_last]
      rw [swap_source_word]
      simpa only [List.map_ofFn] using (payload k).symm
    | cast i => simpa only [caller,Fin.lastCases_castSucc] using headers i k
  have rep : RepT (M8.Machine.ArbitraryWidthOriginalTotalRun.input caller) S.L S.R := by
    rw [LeafCore.input_eq]
    intro i k
    by_cases inside : i.val < 7
    · have atSlot : slot ⟨i.val,inside⟩ = i := Fin.ext rfl
      simpa only [SharedBankStageInput.raw,dite_eq_left inside,atSlot] using read ⟨i.val,inside⟩ k
    · obtain ⟨l,r⟩ := free i (by omega)
      simp [SharedBankStageInput.raw,inside,l,r,readAt_nil_left,wordTape_nil]
  have leaf := M8.Machine.ArbitraryWidthOriginalTotalRun.runs caller Fin.castSucc (Fin.last 6)
    batch (Routines.hdr batch) positive (Routines.hdr_headers batch)
    (fun j => by simp [caller]) (fun j => by simp [caller]) word (by simp only [caller,Fin.lastCases_last]) (by simp only [caller,Fin.lastCases_last])
  have bounded := leaf.consequence (fun _ h => h) (fun _ h => h) (LeafCore.cost_le positive)
  obtain ⟨z,F,_,rfl,out,user,_,_,stock,n,paid,run⟩ := foreign_exec (body := body)
    (liftQ LeafCore.stage1 capacity) (HoareTime.liftQ capacity bounded) u S _ rfl rep
  refine ⟨z,F,n,user,paid,run,?_,stock⟩
  intro k
  have cell := out owner k
  rw [LeafCore.input_eq] at cell
  have inside : owner.val < 7 := (Fin.last 6).isLt
  simp only [SharedBankStageInput.raw,dite_eq_left inside,SharedPlacementAlphabet.setTape,
    show (⟨owner.val,inside⟩ : Fin 7) = Fin.last 6 from rfl,Function.update_self] at cell
  simpa only [swap_source_word,List.map_ofFn] using cell.symm

/-- Install the separators on copies of the six batch headers, transpose the
payload, then erase both stacks of every private tape, including those copies. -/
theorem stoppedDirectoryLeaf_exec [M8.Machine.Net] {Q : ℕ} {P U : Type}
    (capacity : directoryLeafStates ≤ Q) (body : P → Pr P LeafCore.small Q prime U)
    (batch : Descriptor) (positive : batch.Positive) (word : Fin (volume prime batch) → ZMod 2)
    (u : HS LeafCore.small Q prime U) (S : Stacks LeafCore.small prime) :
    let slot := Fin.castLEEmb LeafCore.seven_le
    let owner := slot (Fin.last 6)
    let headers := (Fin.castAddEmb (n := 6) 1).trans slot
    let fields := (List.finRange 6).map headers
    let work := (List.finRange LeafCore.small).filter (· ≠ owner)
    let cost := LeafCore.coreCost (volume prime batch) batch.width
    (∀ j, S.L (headers j) = [] ∧ S.R (headers j) = (Routines.hdr batch j).map bitSymbol) →
    RecordPayload owner (fun _ => blank) 0 word S →
    (∀ j : Fin LeafCore.small, 7 ≤ j.val → S.L j = [] ∧ S.R j = []) →
    ∃ z F n, z.user = u.user ∧ n ≤ cost*(LeafCore.small+5)+8 +
      work.length*(8*volume prime batch+8*cost+8) ∧
      Exec body (((Prog.act (pushMarkers fields)).seq (foreign (liftQ LeafCore.stage1 capacity))).seq (clearWorkTapes work))
        (mk u S) n (mk z F) ∧
      RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) word) F ∧
      ∀ j, j ≠ owner → F.L j = [] ∧ F.R j = [] := by
  intro slot owner headers fields work cost words payload free
  let B := {S with L := fun j => if j ∈ fields then separator :: S.L j else S.L j}
  have mark := Exec.act (body := body) (pushMarkers fields) (mk u S)
  rw [pushMarkers_run _ ((List.nodup_finRange 6).map headers.injective)] at mark
  have low (j) (hj : j ∈ fields) : j.val < 6 := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    exact i.isLt
  have ownerOff : owner ∉ fields := fun h => (Nat.lt_irrefl 6) (low _ h)
  have rest (j : Fin LeafCore.small) (hj : 7 ≤ j.val) : B.L j = [] ∧ B.R j = [] := by
    have outside : j ∉ fields := fun h => by have := low j h; omega
    simpa [B,outside] using free j hj
  have member (j : Fin 6) : headers j ∈ fields := List.mem_map_of_mem (List.mem_finRange j)
  obtain ⟨z,D,n,user,paid,run,out,stock⟩ := directoryLeaf_exec capacity body batch positive word u B
    (by intro j k
        change RadixZeroFill.encodedBinary _ k = readAt blank (B.L (headers j)) (B.R (headers j)) (k-1)
        simp only [B,ite_eq_left (member j),(words j).1,(words j).2,encodedBinary_eq,readAt_single])
    (by change RecordPayload owner (fun _ => blank) 0 word B
        simpa only [RecordPayload,B,ite_eq_right ownerOff] using payload) rest
  obtain ⟨y,same,clear⟩ := clearWorkTapes_exec body work ((List.nodup_finRange _).filter _) z D
  have size (j : Fin LeafCore.small) (hj : j ∈ work) :
      (B.L j).length+(B.R j).length ≤ 2*volume prime batch+1 := by
    by_cases small : j.val < 6
    · let i : Fin 6 := ⟨j.val,small⟩
      have atHeader : headers i = j := Fin.ext rfl
      rw [← atHeader]
      simp only [B,ite_eq_left (member i),(words i).1,(words i).2,List.length_cons,List.length_nil,List.length_map]
      have length := RecursiveRowsNode.header_length batch positive _ (Routines.hdr_headers batch) i
      omega
    · have ne := (List.mem_filter.mp hj).2
      have neOwner : j ≠ owner := by simpa using ne
      have high : 7 ≤ j.val := by
        by_contra! short
        exact neOwner (Fin.ext (by change j.val = 6; omega))
      obtain ⟨l,r⟩ := rest j high
      simp [l,r]
  have priced (j) (hj : j ∈ work) : 4*(D.L j).length+2*(D.R j).length+4 ≤
      8*volume prime batch+8*cost+8 := by have := stock j; have := size j hj; omega
  have total := List.sum_le_sum priced
  simp only [List.map_const',List.sum_replicate_nat] at total
  have untouched : owner ∉ work := by simp [work]
  refine ⟨y,_,_,same.trans user,?_,Exec.seq (Exec.seq mark run) clear,?_,?_⟩
  · change n ≤ cost*(LeafCore.small+5)+6 at paid
    omega
  · simpa only [RecordPayload,ite_eq_right untouched] using out
  · intro j ne
    have inside : j ∈ work := by simp [work,ne]
    simp [inside]

private theorem cleanupCost_le (cost V work tapes : ℕ) (C scale : ℝ)
    (core : (cost : ℝ) ≤ C*scale) (volume : (V : ℝ) ≤ scale)
    (room : 1 ≤ scale) (fits : work ≤ tapes) :
    ((cost*(tapes+5)+8+work*(8*V+8*cost+8) : ℕ) : ℝ) ≤
      ((tapes+5 : ℕ)*C+8+tapes*(16+8*C))*scale := by
  have eight : (8 : ℝ) ≤ 8*scale := le_mul_of_one_le_right (by norm_num) room
  have count : (work : ℝ) ≤ tapes := by exact_mod_cast fits
  push_cast
  calc
    _ ≤ (C*scale)*(tapes+5)+8*scale+
        (tapes : ℝ)*(8*scale+8*(C*scale)+8*scale) := by
      gcongr
    _ = _ := by ring

private theorem stoppedDirectoryTime [M8.Machine.Net] (V b work : ℕ) (positive : 0 < V)
    (fits : work ≤ LeafCore.small) :
    let cost := LeafCore.coreCost V b
    let power := ((max 1 b : ℕ) : ℝ)^M8.Machine.BudgetBound.tau
    ((cost*(LeafCore.small+5)+8+work*(8*V+8*cost+8) : ℕ) : ℝ) ≤
      ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*(V*power) := by
  intro cost power
  have core : (cost : ℝ) ≤ |LeafCore.C| *V*power := RevBudget.coreCost_le V b le_rfl
  have one : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_max_left 1 b)
    M8.Machine.BudgetBound.exponent_range.1.le
  have scale : (V : ℝ) ≤ V*power := le_mul_of_one_le_right (Nat.cast_nonneg _) one
  have room : 1 ≤ (V : ℝ)*power := (by exact_mod_cast positive : (1 : ℝ) ≤ V).trans scale
  exact cleanupCost_le cost V work LeafCore.small |LeafCore.C| (V*power)
    (by simpa only [mul_assoc] using core) scale room fits

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- A stopped scheduled occurrence has an actual host execution at column
capacity, with the scheduled output in batch tape order and clean private tapes. -/
theorem scheduledStoppedDirectory_exec [M8.Machine.Net] {P U : Type}
    (body : P → Pr P LeafCore.small columnCapacity prime U) (node : Descriptor)
    (i : Fin nodeChildren5.length) (w : ℕ) (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) :
    let r := nodeChildren5[i.val]
    let batch := ordinaryDirectoryChild (role node 142080) r (64-r) w
    let scheduled := scheduledChild prime node i
    let e := (scheduledDirectoryCoordinates node i w aligned rows).choose
    let slot := Fin.castLEEmb LeafCore.seven_le
    let owner := slot (Fin.last 6)
    let headers := (Fin.castAddEmb (n := 6) 1).trans slot
    let fields := (List.finRange 6).map headers
    let work := (List.finRange LeafCore.small).filter (· ≠ owner)
    let program := ((Prog.act (pushMarkers fields)).seq (foreign (liftQ LeafCore.stage1 directoryLeafFits))).seq (clearWorkTapes work)
    ∀ (word : Fin (volume prime scheduled) → ZMod 2) (u : HS LeafCore.small columnCapacity prime U)
      (S : Stacks LeafCore.small prime), 0 < volume prime node →
      (∀ j, S.L (headers j) = [] ∧ S.R (headers j) = (Routines.hdr batch j).map bitSymbol) →
      RecordPayload owner (fun _ => blank) 0 (word ∘ e) S →
      (∀ j : Fin LeafCore.small, 7 ≤ j.val → S.L j = [] ∧ S.R j = []) →
      ∃ z F n, z.user = u.user ∧ Exec body program (mk u S) n (mk z F) ∧
        (n : ℝ) ≤ ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
          ((volume prime scheduled : ℝ)*((max 1 scheduled.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        RecordPayload owner (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd scheduled.rows) word ∘ e) F ∧
        ∀ j, j ≠ owner → F.L j = [] ∧ F.R j = [] := by
  intro r batch scheduled e slot owner headers fields work program word u S positive prepared payload free
  have shape := (scheduledDirectoryTranspose node i w aligned rows).1
  have share := (scheduledChild_measures prime node ⟨w+1,aligned⟩ rows i).2
  have pos : 0 < volume prime batch := shape.volume.symm ▸ Nat.pos_of_mul_pos_right (share.symm ▸ positive)
  obtain ⟨z,F,n,user,paid,run,out,clean⟩ := stoppedDirectoryLeaf_exec directoryLeafFits body batch
    (LeafCore.positive_of_volume pos) (word ∘ e) u S prepared payload free
  have fits : work.length ≤ LeafCore.small := (List.length_filter_le ..).trans_eq (List.length_finRange)
  have bound := stoppedDirectoryTime (volume prime batch) batch.width work.length pos fits
  have action := (scheduledDirectoryCoordinates node i w aligned rows).choose_spec.2 word
  refine ⟨z,F,n,user,run,?_,action ▸ out,clean⟩
  have time := (Nat.cast_le (α := ℝ)).mpr paid
  exact (time.trans bound).trans_eq (by rw [show volume prime batch = volume prime scheduled from shape.volume,
    show batch.width = scheduled.width from shape.width])

theorem nine_le_leaf [M8.Machine.Net] : 9 ≤ LeafCore.small := by
  simp only [LeafCore.small, M8.Machine.ArbitraryWidthOriginalZeroBranch.count,
    M8.Machine.ArbitraryWidthOriginalZeroBranch.highCount]
  omega

noncomputable def copyDirectoryHeaders {T n Q : ℕ} {P U : Type} (room : 9 ≤ T) (src : Fin 6 → Fin n) :
    Pr P (n+T) Q prime U :=
  let priv := (Fin.castLEEmb room).trans (Fin.natAddEmb n)
  Record.copyLeafHeaders (fun i => (src i).castAdd T)
    ((Fin.castAddEmb (n := 6) 3).trans priv) (priv 7) (priv 8) (List.finRange 6)

/-- Copy the caller's six batch words into the stopped machine. Only its
payload is shared, so the archived headers can be reused after the call. -/
theorem directoryLeafHeaders_exec [M8.Machine.Net] {n Q : ℕ} {P U : Type}
    (body : P → Pr P (n+LeafCore.small) Q prime U) (src : Fin 6 → Fin n) (port : Fin n)
    (batch : Descriptor) (word : Fin (volume prime batch) → ZMod 2)
    (u : HS (n+LeafCore.small) Q prime U) (S : Stacks (n+LeafCore.small) prime) :
    let source := fun i => (src i).castAdd LeafCore.small
    let slot := Fin.castLEEmb LeafCore.seven_le
    let owner := slot (Fin.last 6)
    let bank := Record.payloadBank port owner
    (∀ i, S.R (source i) = (Routines.hdr batch i).map bitSymbol) →
    RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0 word S →
    (∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) →
    ∃ z F, z.user = u.user ∧ Exec body
      (copyDirectoryHeaders nine_le_leaf src)
      (mk u S) (((List.finRange 6).map (fun i => 6*(S.R (source i)).length+6)).sum+1) (mk z F) ∧
      F.L = S.L ∧ (∀ j : Fin n, F.R (j.castAdd LeafCore.small) = S.R (j.castAdd LeafCore.small)) ∧
      F.R (owner.natAdd n) = [] ∧
      (∀ j : Fin 6, (embStk bank F).L (slot j.castSucc) = [] ∧
        (embStk bank F).R (slot j.castSucc) = (Routines.hdr batch j).map bitSymbol) ∧
      RecordPayload owner (fun _ => blank) 0 word (embStk bank F) ∧
      ∀ j : Fin LeafCore.small, 7 ≤ j.val → (embStk bank F).L j = [] ∧ (embStk bank F).R j = [] := by
  intro source slot owner bank words payload free
  let host := Fin.castLEEmb nine_le_leaf
  let targets := Fin.castAddEmb (n := 6) 3
  have distinct : ∀ i, [targets i,(7 : Fin 9),8].Nodup := by decide
  obtain ⟨z,F,user,run,left,keep,loaded,off⟩ := Record.loadPrivateHeaders_exec
    (Function.Embedding.refl (Fin n)) host src targets 7 8 distinct body u S free
  refine ⟨z,F,user,run,left,keep,?_,?_,?_,?_⟩
  · apply off
    intro i eq
    have h := congrArg Fin.val eq
    change i.val = 6 at h
    omega
  · intro j
    have ne : slot j.castSucc ≠ owner := slot.injective.ne (Fin.castSucc_ne_last j)
    change F.L (bank (slot j.castSucc)) = [] ∧ F.R (bank (slot j.castSucc)) = _
    rw [Record.payloadBank_private _ _ _ ne,left]
    exact ⟨(free _).1,(loaded j).trans (words j)⟩
  · intro k
    change readAt _ (F.L (bank owner)) (F.R (bank owner)) _ = _
    rw [Record.payloadBank_shared,left,keep]
    exact payload k
  · intro j high
    have ne : j ≠ owner := by intro eq; have := congrArg Fin.val eq; change j.val = 6 at this; omega
    change F.L (bank j) = [] ∧ F.R (bank j) = []
    rw [Record.payloadBank_private _ _ _ ne,left]
    refine ⟨(free _).1,off j (fun i eq => ?_)⟩
    have h := congrArg Fin.val eq
    change i.val = j.val at h
    omega

noncomputable def hostedStoppedDirectory [M8.Machine.Net] {n Q : ℕ} {P U : Type} (capacity : columnCapacity ≤ Q)
    (src : Fin 6 → Fin n) (port : Fin n) : Pr P (n+LeafCore.small) Q prime U :=
  let slot := Fin.castLEEmb LeafCore.seven_le
  let owner := slot (Fin.last 6)
  let fields := (List.finRange 6).map ((Fin.castAddEmb (n := 6) 1).trans slot)
  let work := (List.finRange LeafCore.small).filter (· ≠ owner)
  let leaf : Pr Empty LeafCore.small columnCapacity prime U :=
    ((Prog.act (pushMarkers fields)).seq (foreign (liftQ LeafCore.stage1 directoryLeafFits))).seq (clearWorkTapes work)
  Prog.seq (copyDirectoryHeaders nine_le_leaf src)
    (statePlacedNormalized (Record.payloadBank port owner) capacity columnCapacity_pos Empty.elim leaf)

private theorem headerSteps_add {copy k : ℕ} {price : ℝ} (paid : (k : ℝ) ≤ price) :
    ((copy+(1+k) : ℕ) : ℝ) ≤ ((copy+1 : ℕ) : ℝ)+price := by
  push_cast
  linarith

private theorem payloadBank_output {n T N : ℕ} (port : Fin n) (owner : Fin T)
    (word : Fin N → ZMod 2) (F : Stacks (n+T) prime) (B : Stacks T prime)
    (onBank : embStk (Record.payloadBank port owner) F = B)
    (out : RecordPayload owner (fun _ => blank) 0 word B) :
    RecordPayload (port.castAdd T) (fun _ => blank) 0 word F := by
  subst B
  intro t
  have hit := out t
  simpa only [embStk,Function.comp_apply,Record.payloadBank_shared] using hit

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Execute a stopped scheduled call directly from its six caller header words.
The caller keeps its other stacks and the entire private suffix is reusable. -/
theorem hostedStoppedDirectory_exec [M8.Machine.Net] {n Q : ℕ} {P U : Type} (capacity : columnCapacity ≤ Q)
    (body : P → Pr P (n+LeafCore.small) Q prime U) (src : Fin 6 → Fin n) (port : Fin n)
    (node : Descriptor) (i : Fin nodeChildren5.length) (w : ℕ) (aligned : node.width = 64*(w+1))
    (rows : 142080 ∣ node.rows) :
    let r := nodeChildren5[i.val]
    let batch := ordinaryDirectoryChild (role node 142080) r (64-r) w
    let scheduled := scheduledChild prime node i
    let e := (scheduledDirectoryCoordinates node i w aligned rows).choose
    let source := fun i => (src i).castAdd LeafCore.small
    ∀ (word : Fin (volume prime scheduled) → ZMod 2) (u : HS (n+LeafCore.small) Q prime U)
      (S : Stacks (n+LeafCore.small) prime), 0 < volume prime node →
      (∀ j, S.R (source j) = (Routines.hdr batch j).map bitSymbol) →
      RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0 (word ∘ e) S →
      (∀ j : Fin LeafCore.small, S.L (j.natAdd n) = [] ∧ S.R (j.natAdd n) = []) →
      ∃ (z : HS (n+LeafCore.small) Q prime U) (F : Stacks (n+LeafCore.small) prime) (steps : ℕ), z.user = u.user ∧
        Exec body (hostedStoppedDirectory capacity src port)
          (mk u S) steps (mk z F) ∧
        (steps : ℝ) ≤ descriptorHeaderCost batch +
          ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
          ((volume prime scheduled : ℝ)*((max 1 scheduled.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau) ∧
        RecordPayload (port.castAdd LeafCore.small) (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd scheduled.rows) word ∘ e) F ∧
        (∀ j : Fin n, j ≠ port → F.L (j.castAdd LeafCore.small) = S.L (j.castAdd LeafCore.small) ∧ F.R (j.castAdd LeafCore.small) = S.R (j.castAdd LeafCore.small)) ∧
        ∀ j : Fin LeafCore.small, F.L (j.natAdd n) = [] ∧ F.R (j.natAdd n) = [] := by
  intro r batch scheduled e source word u S positive words payload free
  let owner := (Fin.castLEEmb LeafCore.seven_le) (Fin.last 6)
  let bank := Record.payloadBank port owner
  obtain ⟨v,D,user,setup,left,keep,unused,prepared,input,rest⟩ :=
    directoryLeafHeaders_exec (n := n) (Q := Q) body src port batch (word ∘ e) u S words payload free
  obtain ⟨y,B,k,same,run,paid,out,clean⟩ := scheduledStoppedDirectory_exec (P := Empty) Empty.elim
    node i w aligned rows word (stateLiftDown columnCapacity_pos (embDn bank v)) (embStk bank D)
    positive prepared input rest
  obtain ⟨z,_,user',placed⟩ := statePlaced_exec_normalized bank bank.injective capacity columnCapacity_pos
    Empty.elim (body' := body) (fun f => nomatch f) v D run
  let F := embOvr bank B.get D
  have onBank : embStk bank F = B := embStk_ovr bank.injective _ _
  have apart (j : Fin LeafCore.small) (l : Fin n) : j.natAdd n ≠ l.castAdd LeafCore.small := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_natAdd,Fin.val_castAdd] at h
    omega
  have seqRun := Exec.seq setup placed
  let init := ((List.finRange 6).map fun j => 6*(S.R (source j)).length+6).sum+1
  refine ⟨z,F,init+(1+k),?_,?_,?_,?_,?_,?_⟩
  · simp only [stateLiftDown,embDn] at same
    exact user'.trans (same.trans user)
  · unfold hostedStoppedDirectory
    exact seqRun
  · have hdr (j) : (S.R ((src j).castAdd LeafCore.small)).length = (Routines.hdr batch j).length := by
      rw [show S.R ((src j).castAdd LeafCore.small) = _ from words j,List.length_map]
    simp only [init,source,hdr]
    exact headerSteps_add paid
  · exact payloadBank_output port owner _ F B onBank out
  · intro j ne
    have off : ∀ l, bank l ≠ j.castAdd LeafCore.small := by
      intro l
      by_cases h : l = owner
      · subst l
        rw [Record.payloadBank_shared]
        exact (Fin.castAddEmb _).injective.ne ne.symm
      · rw [Record.payloadBank_private _ _ _ h]
        exact apart _ _
    obtain ⟨l,r'⟩ := embOvr_off B.get D off
    exact ⟨l.trans (congrFun left _),r'.trans (keep j)⟩
  · intro j
    by_cases h : j = owner
    · subst j
      have off : ∀ l, bank l ≠ owner.natAdd n := by
        intro l
        by_cases h : l = owner
        · subst l
          rw [Record.payloadBank_shared]
          exact (apart _ _).symm
        · rw [Record.payloadBank_private _ _ _ h]
          exact (Fin.natAddEmb n).injective.ne h
      obtain ⟨l,r'⟩ := embOvr_off B.get D off
      exact ⟨l.trans ((congrFun left _).trans (free _).1),r'.trans unused⟩
    · have erased := clean j h
      rw [← onBank] at erased
      simpa only [embStk,Function.comp_apply,bank,Record.payloadBank_private _ _ _ h] using erased

end IntegerMultBounds.MathlibTM2.M6.BitNode
