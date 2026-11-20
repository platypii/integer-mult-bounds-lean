module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryScan

/-! Execute the scheduled remainder scanner from the parent's packed prefix and owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback M8.RevMachine
open IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Swap.Modular Matrix
open LabelTraversal FlatCoordinateLayout

def OrdinaryParentRun [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (layout : Descriptor)
    (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (overhead childBudget : ℕ)
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U) : Prop :=
    let K := common+24+31+work
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let W := layout.between*layout.afterD
    let N := M^128*W
    let directory := role layout 142080
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    let placement := directoryOrdinaryBank room
    let bank := (Fin.castLEEmb (show 72 ≤ 66+(K+1) by omega)).trans (Fin.castAddEmb 5)
    let reg := fun i : Fin 5 => i.natAdd (66+(K+1))
    let body := fun f => embProg placement id (localBody f)
    let outer := fun f => embProg (fun i : Fin (66+(K+1)) => i.castAdd 5) id (body f)
    let parents := layout.beforeRows*rows*B
    let box := M^(64*64)
    let data : ScanData 64 127 w W := {
      records := LabelMask.records directory, H := M.size, J := W.size,
      table := fun _ => 0, matrix := fun _ => 0, input := fun _ _ => 0,
      signed := [], matrixTail := [], pivotTail := [], inputTail := [], outputTail := [] }
    ∀ (u : HS ((66+(K+1))+5) columnCapacity prime U) (raw : Stacks ((66+(K+1))+5) prime)
      (word : Fin (data.records*N) → ZMod 2) (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))),
    let setupScratch := ([0,4,9,10,11,12] : List (Fin 15)).map (remainderDirectoryPorts.trans bank) ++ [bank 71]
    let inherited := (setupScratch.map (fun i => 4*(raw.L i).length)).sum+2*tail.length
    let setupTime := ((366+16*64*64+19*64+344)*volume prime layout+prime^layout.width*inherited*142080)/(prime^layout.width*142080)
    let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let left := (privateTapes.map fun i => 4*(raw.L ((placement i).castAdd 5)).length).sum
    let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    let ports := ordinaryCursorPorts.trans (Fin.castAddEmb (n := 66) K)
    let step := (ordinaryRowCore (U := U) (Q := columnCapacity) (le_max_left ..) 64 proj.rank proj.rank_le_height pool space).seq
      (readWithSuccessorClock (ports 1) (advanceDirectory 64 ports))
    let push := max (mnProgPush step) (mnProgPush (localBody ()))
    let rarePush := max (mnProgPush (directoryExceptionalCore (P := Unit) (U := U) 127 room remainderAnchorFits)) (mnProgPush (body ()))
    let rate := exceptionalVolumeRate U 127 64 scratch.length rarePush w
    (raw.R (bank 29)).length = layout.beforeRows → (raw.R (bank 30)).length = rows → (raw.R (bank 31)).length = layout.beforeH →
    (∀ i : Fin (66+(K+1)), 59 ≤ i.val → raw.R (i.castAdd 5) = []) →
    raw.R (bank 58) = (List.range parents).flatMap prefixes ++ tail →
    (∀ i < parents, (prefixes i).length = (raw.R (bank 47)).length) →
    (raw.R (bank 47)).length ≤ prime^layout.width →
    raw.R (bank 28) = [] → raw.R (bank 44) = [] → raw.R (bank 49) = [] →
    ParentParameters root W data.H W.size parent (fun i => raw.R (bank (i.castLE (by decide)))) →
    raw.R (bank 50) = [] → raw.R (bank 57) = [] → raw.R (bank 56) = [] → raw.R (bank 54) = [] →
    (∀ j, readAt blank (raw.L (reg 0)) (raw.R (reg 0)) j = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j)) →
    (∀ i : Fin 5, i ≠ 0 → raw.R (reg i) = []) →
    (∀ j, readAt blank (raw.L (bank 24)) (raw.R (bank 24)) j = blank) →
    let embed := fun i : Fin (66+(K+1)) => i.castAdd 5
    ∃ selectors prepare dispatch z F t output,
      let controls := embProg embed id (embProg placement id selectors)
      let scan := (payloadCountProgram (ownerCountPorts (K+1)) 128).seq (controls.seq ((embProg embed id prepare).seq dispatch))
      z.user = u.user ∧ Exec outer ((remainderOwnerSetup root interval.1 interval.2 bank).seq scan) (mk u raw) t (mk z F) ∧
      (∀ p, mnProgPush (prepare : Pr Unit (66+(K+1)) columnCapacity prime U) ≤ p → mnProgPush (body ()) ≤ p →
        t ≤ setupTime+ordinaryOwnerScanTime 64 127 proj.rank w W data.H W.size data.records N
          (prefixes 0).length (raw.R (bank 46)).length (raw.R (bank 48)).length left privateTapes.length push scratch.length rate p overhead childBudget) ∧
      (∀ j : Fin data.records, let r := ownerRow (R := data.records) (N := N) rfl output j
        if LabelStock.live 64 (w+1) 1 j then ∀ x k, r (index ((projectorResidual finSumFinEquiv (reduce M proj)
          parent (fun i => Ring.inverse (parent i)) (physicalLabel 64 (w+1) j)).mulVec x) k) = ownerRow (R := data.records) (N := N) rfl word j (index x k)
        else ownerRow (R := data.records) (N := N) rfl word j = r) ∧
      (∀ (c : Certificates.PR589.Nine.PortCertificate), c.Checked → ∀ block < parents,
        ∀ (g : LabelPadding.Label 64 (w+1)), IsUnit g →
        let chart := reduce M (c.fullChart.submatrix stageAxis.symm remainderAxis)
        let P := reduce M ((c.span interval.1 interval.2).submatrix stageAxis.symm stageAxis.symm)
        let j := block*box+(LabelAddress.address (g*chart)).val
        ∀ x k, ownerRow (R := data.records) (N := N) rfl output j
          (index ((projectorResidual finSumFinEquiv P parent (fun i => Ring.inverse (parent i)) g).mulVec x) k) =
            ownerRow (R := data.records) (N := N) rfl word j (index x k)) ∧
      (∀ j, readAt blank (F.L (reg 0)) (F.R (reg 0)) j = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 ((List.ofFn output).map SparseRoleCircuit.encode) j)) ∧
      F.L (reg 0) = raw.L (reg 0) ∧ F.R (reg 0) = payloadWord (SparseRoleCircuit.encode ∘ output) ++
        (raw.R (reg 0)).drop (data.records*N) ∧ F.R (reg 1) = [] ∧
      F.R ((directoryMatrixTape room).castAdd 5) = [] ∧ F.R (bank 57) = [] ∧ F.R (bank 56) = []

private theorem ordinaryParent_exec [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals) (layout : Descriptor)
    (positive : layout.Positive) (width : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
    (shape : layout.beforeH = B*prime^(64*((w+1)*64))) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) (overhead childBudget : ℕ)
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U)
    (scan : ∀ (data : ScanData 64 127 w (layout.between*layout.afterD)), data.H = (prime^(w+1)).size →
      ∀ prefixes archiveTail ownerTail, ClassifiedOrdinaryScan (a := 63) (J := (layout.between*layout.afterD).size)
        (remainderRecordChild interval.1 interval.2 (w+1) (layout.between*layout.afterD))
        (diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0) (by decide)
        parent data room fits remainderAnchorFits pool space (le_max_left ..) overhead childBudget prefixes archiveTail ownerTail localBody) :
    OrdinaryParentRun (rows := rows) (B := B) interval layout root parent room pool space overhead childBudget localBody := by
  unfold OrdinaryParentRun
  intro K M W N directory proj placement bank reg body outer parents box data u raw word prefixes tail
    setupScratch inherited setupTime privateTapes left scratch ports step push rarePush rate br nr bh clean source widths fitsWidth
    short padded spare parameters parentPort mask mode queue payload empty blankData
  let v := remainderRecordChild interval.1 interval.2 (w+1) W
  have binary : data.H = M.size := rfl
  have count : data.records = LabelMask.records directory := rfl
  letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
  obtain ⟨ordered,upper,_⟩ := BitHosting.remainder_counts interval member
  obtain ⟨y,D,q,user,paid,build,input,free,matrix,right,leftEq,size,regs⟩ := remainderDirectory_prepareOwner
    (by omega) outer layout v w rows B W data.H W.size positive width split shape interval.1 interval.2 binary rfl rfl
    ordered (by omega) (by intro i; fin_cases i <;> rfl) root parent prefixes tail u raw br nr bh clean source widths fitsWidth short padded spare parameters
  let start := embStk (fun i : Fin (66+(K+1)) => i.castAdd 5) D
  let whole := embStk placement start
  have shared (i : Fin 58) : whole.R ((i.castAdd 8).castAdd K) = D.R (bank (i.castLE (by decide))) := by
    change D.R ((placement ((i.castAdd 8).castAdd K)).castAdd 5) = _
    rw [directoryOrdinaryBank_caller]; rfl
  have frame (i : Fin 58) (off : i ∉ ([28,33,34,35,36,37,38,44,46,48,55] : List (Fin 58))) :=
    (shared i).trans (right i off)
  have workEmpty (i : Fin (66+K)) (hi : 58 ≤ i.val) : whole.R i = [] := by
    apply free
    by_contra! lo
    let j : Fin 66 := ⟨(placement i).val,by omega⟩
    have eq : placement i = placement (j.castAdd K) := by rw [directoryOrdinaryBank_caller]; exact Fin.ext rfl
    have h := congrArg Fin.val (placement.injective eq)
    change i.val = (placement i).val at h
    omega
  have rolePositive := RecursiveRowsNodeLayout.role_positive 142080 layout (by decide) positive ⟨rows,split⟩
  have roleRows : directory.rows = rows := by simp [directory,role,split]
  have saved (i : Fin 5) (hi : i ≠ 0) := (regs i).1.trans (empty i hi)
  have packed := payload_prefix_of_read word (fun _ => blank) 0 (raw.L (reg 0)) (raw.R (reg 0)) (by simpa only [sub_zero] using payload)
  let archive := fun j => prefixes (j/box)
  obtain ⟨selectors,prepare,z,F,t,n,output,k,s,midUser,mid,_,same,_,_,_,_,time,run,action,reads,ownerLeft,ownerRight,accumulator,_,clear,maskEnd,modeEnd⟩ :=
    scan data binary archive (raw.R (bank 46)) ((raw.R (reg 0)).drop (data.records*N)) word directory B y D
      (free _ (by have h := directoryMatrixTape_private room; omega)) rolePositive shape count pairRoom workEmpty
      (by
        change DirectoryScanInput v proj w W data.H W.size parent archive _ (List.range data.records)
          (fun i : Fin 58 => whole.R ((i.castAdd 8).castAdd K))
        rw [count,funext shared]
        exact input) ((congrArg List.length (frame 29 (by decide))).trans br)
      (((congrArg List.length (frame 30 (by decide))).trans nr).trans roleRows.symm)
      ((congrArg List.length (frame 31 (by decide))).trans bh) ((frame 50 (by decide)).trans parentPort)
      ((frame 57 (by decide)).trans mask) ((frame 56 (by decide)).trans mode) ((frame 54 (by decide)).trans queue)
      ((regs 0).1.trans packed) (by intro j; rw [(regs 0).1,(regs 0).2]; exact payload j)
      (saved 1 (by decide)) (saved 2 (by decide)) (saved 3 (by decide)) (saved 4 (by decide))
      (by intro j; change readAt blank (D.L (bank 24)) (D.R (bank 24)) j = blank
          have hl : D.L (bank 24) = raw.L (bank 24) := leftEq 24
          have hr : D.R (bank 24) = raw.R (bank 24) := right 24 (by decide)
          rw [hl,hr]; exact blankData j)
  have coord : finSumFinEquiv.trans (finCongr (by decide : 64+64 = 127+1)) = finSumFinEquiv := by ext i; rfl
  refine ⟨selectors,prepare,_,z,F,_,output,same.trans user,Exec.seq build run,?_,?_,?_,reads,
    ownerLeft.trans (regs 0).2,ownerRight,accumulator,clear,maskEnd,modeEnd⟩
  · intro p bound calls
    have setup : q ≤ setupTime := by
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) (by decide))).mpr
      simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using paid
    have parentsPos : 0 < parents := by
      have rowsPos : 0 < rows := roleRows ▸ rolePositive.2.1
      have bPos : 0 < B := by
        by_contra! hz
        have := positive.2.2.1
        simp [shape,Nat.eq_zero_of_le_zero hz] at this
      exact Nat.mul_pos (Nat.mul_pos positive.1 rowsPos) bPos
    have first : (archive 0).length ≤ N := by
      rw [show archive 0 = prefixes 0 by simp [archive], widths 0 parentsPos]
      apply fitsWidth.trans
      have powLe : M^64 ≤ M^128 := Nat.pow_le_pow_right (pow_pos Shared50ModularControl.prime_prime.pos _) (by decide)
      rw [width,Nat.mul_comm 64 (w+1),pow_mul]
      exact powLe.trans (Nat.le_mul_of_pos_right _ (Nat.mul_pos positive.2.2.2.1 positive.2.2.2.2))
    have scanBound := time p bound (fun f => by cases f; exact calls) first
    have suffix : (whole.R ((48 : Fin 66).castAdd K)).drop (64*64*data.H) = raw.R (bank 48) := by
      rw [show whole.R ((48 : Fin 66).castAdd K) = D.R (bank 48) from shared 48,matrix,
        ← length_matrixWords prime data.H (reduce M proj),List.drop_left]
    have leftBound : (privateTapes.map (fun i => 4*(whole.L i).length)).sum ≤ left :=
      List.sum_le_sum (fun i hi => Nat.mul_le_mul_left 4 (size ((placement i).castAdd 5)))
    apply Nat.add_le_add setup
    apply scanBound.trans
    change ordinaryOwnerScanTime 64 127 proj.rank w W data.H W.size data.records N (archive 0).length
      (raw.R (bank 46)).length ((whole.R ((48 : Fin 66).castAdd K)).drop (64*64*data.H)).length
      (privateTapes.map (fun i => 4*(whole.L i).length)).sum privateTapes.length push scratch.length rate p overhead childBudget ≤ _
    rw [show archive 0 = prefixes 0 by simp [archive],suffix]
    unfold ordinaryOwnerScanTime
    exact Nat.add_le_add_left (Nat.add_le_add_right (Nat.add_le_add_right leftBound _) _) _
  · intro j
    simpa only [Fin.cast_refl,id_eq,coord] using action j
  · intro c checked block inside g unit chart P j
    have pos : j < data.records := by
      rw [count, remainderDirectoryCount layout w rows B split shape]
      calc
        j < block*box+box := Nat.add_lt_add_left (LabelAddress.address (g*chart)).isLt _
        _ = (block+1)*box := (Nat.succ_mul ..).symm
        _ ≤ parents*box := Nat.mul_le_mul_right _ inside
    apply ownerRow_projected (R := data.records) (N := N) (W := W) rfl rfl word output c checked interval.1 interval.2 upper
      block g unit parent (fun i => Ring.inverse (parent i))
    simpa only [Fin.cast_refl,id_eq,coord] using action ⟨j,pos⟩

/-- A single installed body handles every precision and every parent at this interval. -/
theorem scheduledOrdinaryParent_exec [M8.Machine.Net] {common work : ℕ} {U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals)
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
    (pairRoom : 64*64+64*64 ≤ common+24+31+work) :
    ∃ T, ∃ localBody : Unit → Pr Unit (66+(common+24+31+(work+T))) columnCapacity prime U,
    ∃ C : ℝ, ∃ overhead : ℕ, ∀ (layout : Descriptor) (w rows B : ℕ) (positive : layout.Positive)
      (width : layout.width = 64*(w+1)) (split : layout.rows = 142080*rows)
      (shape : layout.beforeH = B*prime^(64*((w+1)*64))),
      let W := layout.between*layout.afterD
      ∃ budget : ℕ, (budget : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*((prime^(w+1))^128*W : ℕ) ∧
      ∀ root (parent : Fin 64 → ZMod (prime^(w+1))), (∀ i, IsUnit (parent i)) →
        OrdinaryParentRun (common := common) (work := work+T) (rows := rows) (B := B) interval layout
          root parent (by omega) (pool.trans (by omega)) (by omega) overhead budget localBody := by
  obtain ⟨T,body,C,overhead,installed⟩ := scheduledOrdinaryScan_exec (U := U) interval member space pool room fits
  refine ⟨T,body,C,overhead,?_⟩
  intro layout w rows B positive width split shape W
  obtain ⟨budget,paid,scan⟩ := installed w W (Nat.mul_pos positive.2.2.2.1 positive.2.2.2.2)
  refine ⟨budget,paid,?_⟩
  intro root parent unit
  apply ordinaryParent_exec (common := common) (work := work+T) interval member layout positive width split shape root parent
    (room.trans (by omega)) (fits.trans (by omega)) (pool.trans (by omega)) (space.trans (by omega)) (pairRoom.trans (by omega)) overhead budget body
  exact scan _ parent unit

end IntegerMultBounds.MathlibTM2.M6.BitNode
