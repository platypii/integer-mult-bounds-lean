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

end IntegerMultBounds.MathlibTM2.M6.BitNode
