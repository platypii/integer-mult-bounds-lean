module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryScan
public import IntegerMultBounds.MathlibTM2.StackBankStock

/-! Execute the scheduled remainder scanner from the parent's packed prefix and owner tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume role)
open IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback M8.RevMachine
open IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Swap.Modular Matrix
open LabelTraversal FlatCoordinateLayout

/-- Stacks whose inherited contents contribute to the parent setup or scan. -/
def ordinaryInheritedBank {T : ℕ} (setup scan : List (Fin T)) (bank : Fin 72 ↪ Fin T) : Finset (HK T) :=
  ((setup++scan).toFinset.map ⟨HK.lt,fun _ _ h => HK.lt.inj h⟩) ∪
    ((([58,46,48] : List (Fin 72)).map bank).toFinset.map ⟨HK.rt,fun _ _ h => HK.rt.inj h⟩)

private theorem ordinaryInheritedBank_stock {T Q : ℕ} {U : Type} (u : HS T Q prime U) (S : Stacks T prime)
    (setup scan : List (Fin T)) (bank : Fin 72 ↪ Fin T) :
    (∑ i ∈ (setup++scan).toFinset, (S.L i).length) +
      (∑ i ∈ (([58,46,48] : List (Fin 72)).map bank).toFinset, (S.R i).length) =
        bankStock (ordinaryInheritedBank setup scan bank) (mk u S) := by
  unfold bankStock ordinaryInheritedBank
  rw [Finset.sum_union,Finset.sum_map,Finset.sum_map]
  · rfl
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨_,_,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨_,_,h⟩ := Finset.mem_map.mp hj
    cases h

/-- Each left stack can be billed in both setup and scanning. The three inherited
right-hand words occupy distinct tapes. -/
private theorem inherited_le_stock {T Q : ℕ} {U : Type} (u : HS T Q prime U) (S : Stacks T prime)
    (setup scan : List (Fin T)) (hs : setup.Nodup) (hc : scan.Nodup) (bank : Fin 72 ↪ Fin T)
    (tail rate : ℕ) (ht : tail ≤ (S.R (bank 58)).length) :
    (setup.map (fun i => 4*(S.L i).length)).sum + 2*tail +
      ((scan.map (fun i => 4*(S.L i).length)).sum + rate*((S.R (bank 46)).length+(S.R (bank 48)).length)) ≤
      max 8 (max 2 rate)*bankStock (ordinaryInheritedBank setup scan bank) (mk u S) := by
  let ls := (setup++scan).toFinset
  let rs := ([58,46,48] : List (Fin 72)).map bank
  let L := ∑ i ∈ ls, (S.L i).length
  let R := ∑ i ∈ rs.toFinset, (S.R i).length
  let c := max 8 (max 2 rate)
  have left (ks : List (Fin T)) (unique : ks.Nodup) (sub : ks.toFinset ⊆ ls) :
      (ks.map (fun i => 4*(S.L i).length)).sum ≤ 4*L := by
    rw [← List.sum_toFinset _ unique,Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset sub
  have right := List.sum_toFinset (fun i => (S.R i).length)
    (List.Nodup.map bank.injective (by decide : ([58,46,48] : List (Fin 72)).Nodup))
  change R = (S.R (bank 58)).length+((S.R (bank 46)).length+((S.R (bank 48)).length+0)) at right
  have size := ordinaryInheritedBank_stock u S setup scan bank
  have cr : rate ≤ c := (le_max_right 2 rate).trans (le_max_right ..)
  have ct : 2 ≤ c := (le_max_left 2 rate).trans (le_max_right ..)
  have controls := Nat.mul_le_mul_right L (show 8 ≤ c from le_max_left ..)
  have tails := Nat.mul_le_mul_right ((S.R (bank 46)).length+(S.R (bank 48)).length) cr
  have head := Nat.mul_le_mul ct ht
  have bound := congrArg (c*·) right
  calc
    _ ≤ c*(L+R) := by
      have := left setup hs (by simp [ls])
      have := left scan hc (by simp [ls])
      simp only [Nat.add_zero,Nat.mul_add] at bound tails ⊢
      omega
    _ = _ := congrArg (c*·) size

/-- Private right tapes at a fresh scanner entry. The packed owner itself is
on a separate register, so these words can be fixed before the chart runs. -/
noncomputable def ordinaryEntryWords {w : ℕ} (W beforeRows rows beforeH : ℕ) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (width : ℕ) (prefixes : List (Fin (prime+4))) :
    ℕ → List (Fin (prime+4))
  | 2 => binSyms (prime^(w+1)).size (prime^(w+1))
  | 29 => List.replicate beforeRows (bitSymbol true)
  | 30 => List.replicate rows (bitSymbol true)
  | 31 => List.replicate beforeH (bitSymbol true)
  | 45 => List.replicate w (bitSymbol true)
  | 47 => List.replicate width (bitSymbol true)
  | 53 => binSyms W.size W
  | 55 => if root then [] else (List.ofFn fun i => binSyms (prime^(w+1)).size (parent i).val).flatten
  | 58 => prefixes
  | _ => []

theorem ordinaryEntryWords_parameters {w : ℕ} (W beforeRows rows beforeH : ℕ) (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1))) (width : ℕ) (prefixes : List (Fin (prime+4)))
    (units : root = true → ∀ i, parent i = 1) :
    ParentParameters root W (prime^(w+1)).size W.size parent
      (fun i => ordinaryEntryWords W beforeRows rows beforeH root parent width prefixes i.val) := by
  cases root
  · exact ⟨rfl,rfl,fun i => by fin_cases i <;> rfl,List.length_replicate,rfl⟩
  · exact ⟨units rfl,rfl,rfl,fun i => by fin_cases i <;> rfl,List.length_replicate,rfl⟩

/-- Combine the private metadata with the payload delivered by the chart. -/
noncomputable def ordinaryEntryStacks {T N : ℕ} (metadata : ℕ → List (Fin (prime+4)))
    (word : Fin N → ZMod 2) : Stacks (T+5) prime where
  inp := []
  out := []
  L := fun _ => []
  R := Fin.addCases (fun i => metadata i.val)
    (fun i : Fin 5 => if i = 0 then payloadWord (SparseRoleCircuit.encode ∘ word) else [])

theorem ordinaryEntryStacks_payload {T N : ℕ} (metadata : ℕ → List (Fin (prime+4)))
    (word : Fin N → ZMod 2) (j : ℤ) :
    let S := ordinaryEntryStacks (T := T) metadata word
    readAt blank (S.L ((0 : Fin 5).natAdd T)) (S.R ((0 : Fin 5).natAdd T)) j =
      RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j) := by
  simpa [ordinaryEntryStacks,M8.AtomBank.arrTape,List.map_ofFn,Function.comp_def] using
    (payload_reads (SparseRoleCircuit.encode ∘ word) j).symm

/-- With the prefix queue packed to its exact length, fresh private tapes
contribute zero to the inherited part of the scanner's time bound. -/
theorem ordinaryEntryStacks_inherited {T N w : ℕ} (room : 72 ≤ T)
    (W beforeRows rows beforeH : ℕ) (root : Bool) (parent : Fin 64 → ZMod (prime^(w+1)))
    (width : ℕ) (prefixes : List (Fin (prime+4))) (word : Fin N → ZMod 2)
    (setup scan : List (Fin (T+5))) (rate : ℕ) :
    let S := ordinaryEntryStacks (T := T) (ordinaryEntryWords W beforeRows rows beforeH root parent width prefixes) word
    let bank := (Fin.castLEEmb room).trans (Fin.castAddEmb 5)
    (setup.map (fun i => 4*(S.L i).length)).sum +
      ((scan.map (fun i => 4*(S.L i).length)).sum + rate*((S.R (bank 46)).length+(S.R (bank 48)).length)) = 0 := by
  change (setup.map (fun _ => 0)).sum + ((scan.map (fun _ => 0)).sum + rate *
    (((ordinaryEntryStacks (T := T) _ word).R (((46 : Fin 72).castLE room).castAdd 5)).length +
    ((ordinaryEntryStacks (T := T) _ word).R (((48 : Fin 72).castLE room).castAdd 5)).length)) = 0
  simp [ordinaryEntryStacks,ordinaryEntryWords]

def OrdinaryParentRun [M8.Machine.Net] {common work w rows B : ℕ} {U : Type}
    (interval : ℕ × ℕ) (layout : Descriptor)
    (root : Bool)
    (parent : Fin 64 → ZMod (prime^(w+1)))
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1)
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
    ∃ selectors : Pr Unit (66+K) columnCapacity prime U,
    ∀ (u : HS ((66+(K+1))+5) columnCapacity prime U) (raw : Stacks ((66+(K+1))+5) prime)
      (word : Fin (data.records*N) → ZMod 2) (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))),
    let setupScratch := ([0,4,9,10,11,12] : List (Fin 15)).map (remainderDirectoryPorts.trans bank) ++ [bank 71]
    let inherited := (setupScratch.map (fun i => 4*(raw.L i).length)).sum+2*tail.length
    let setupBase := ((366+16*64*64+19*64+344)*volume prime layout)/(prime^layout.width*142080)
    let setupTime := setupBase+inherited
    let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let scanned := privateTapes.map (fun i => (placement i).castAdd 5)
    let visited := ordinaryInheritedBank setupScratch scanned bank
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
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let inner := Fin.castAddEmb (n := 66) K
    let advance := dropWords (placement (inner 2)) (directoryMatrixTape room) (placement (inner 59)) (128*128)
    let good := (embProg placement id (step.seq (clearWorkTapes privateTapes))).seq advance
    let padding := (embProg placement id (readWithSuccessorClock (ports 1) (advanceDirectory 64 ports))).seq advance
    let dispatch := packedOwner (caller 24) (caller 57) (ownerDispatch (caller 57) (caller 56) good
      (directoryExceptionalProgram 64 127 room remainderAnchorFits) padding)
    ∃ prepare z F t output,
      let controls := embProg embed id (embProg placement id selectors)
      let scan := (payloadCountProgram (ownerCountPorts (K+1)) 128).seq (controls.seq ((embProg embed id prepare).seq dispatch))
      z.user = u.user ∧ Exec outer ((remainderOwnerSetup root interval.1 interval.2 bank).seq scan) (mk u raw) t (mk z F) ∧
      (let p := max (mnProgPush (directoryQueueInitProgram (m := 64) (d := 127) (P := Unit) (Q := columnCapacity) (U := U) room fits)) (mnProgPush (body ()))
       let tapeRate := (1+scratch.length*(6*p))*directoryQueueInitRate 64 127
       let clean := setupBase+ordinaryOwnerScanTime 64 127 proj.rank w W data.H W.size data.records N
          (prefixes 0).length 0 0 0 privateTapes.length push scratch.length rate p overhead childBudget
       t ≤ clean+(inherited+(left+tapeRate*((raw.R (bank 46)).length+(raw.R (bank 48)).length))) ∧
       ∀ {P : Type} (priorBody : P → _) prior initial n c, Exec priorBody prior initial n (mk u raw) →
         bankProgPush visited prior ≤ c → (∀ f, bankProgPush visited (priorBody f) ≤ c) →
         t ≤ clean+max 8 (max 2 tapeRate)*(bankStock visited initial+c*n)) ∧
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
      F.R ((directoryMatrixTape room).castAdd 5) = [] ∧ F.R (bank 57) = [] ∧ F.R (bank 56) = [] ∧
      F.R (bank 46) = raw.R (bank 46) ∧ bankStock visited (mk z F) = (raw.R (bank 46)).length+(F.R (bank 48)).length ∧
      ∀ i : Fin (66+K), 58 ≤ i.val → F.L ((placement i).castAdd 5) = [] ∧ F.R ((placement i).castAdd 5) = []

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
      ClassifiedOrdinaryScan (a := 63) (J := (layout.between*layout.afterD).size)
        (remainderRecordChild interval.1 interval.2 (w+1) (layout.between*layout.afterD))
        (diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0) (by decide)
        parent data room fits remainderAnchorFits pool space (le_max_left ..) overhead childBudget localBody) :
    OrdinaryParentRun (rows := rows) (B := B) interval layout root parent room fits pool space overhead childBudget localBody := by
  unfold OrdinaryParentRun
  intro K M W N directory proj placement bank reg body outer parents box data
  have rolePositive := RecursiveRowsNodeLayout.role_positive 142080 layout (by decide) positive ⟨rows,split⟩
  obtain ⟨selectors,execute⟩ := scan data rfl directory B rolePositive shape pairRoom
  refine ⟨selectors,?_⟩
  intro u raw word prefixes tail
    setupScratch inherited setupBase setupTime privateTapes scanned visited left scratch ports step push rarePush rate br nr bh clean source widths fitsWidth
    short padded spare parameters parentPort mask mode queue payload empty blankData caller inner advance good padding dispatch
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
  have roleRows : directory.rows = rows := by simp [directory,role,split]
  have saved (i : Fin 5) (hi : i ≠ 0) := (regs i).1.trans (empty i hi)
  have packed := payload_prefix_of_read word (fun _ => blank) 0 (raw.L (reg 0)) (raw.R (reg 0)) (by simpa only [sub_zero] using payload)
  let archive := fun j => prefixes (j/box)
  obtain ⟨prepare,z,F,t,n,output,k,s,midUser,mid,_,same,_,_,_,_,time,run,action,reads,ownerLeft,ownerRight,accumulator,done,clear,maskEnd,modeEnd⟩ :=
    execute archive (raw.R (bank 46)) ((raw.R (reg 0)).drop (data.records*N)) word y D (free _ (by have h := directoryMatrixTape_private room; omega)) count workEmpty
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
  have restored : F.R (bank 46) = raw.R (bank 46) := by
    have h := done.1
    change F.R ((placement ((46 : Fin 66).castAdd K)).castAdd 5) = _ at h
    rw [directoryOrdinaryBank_caller] at h
    exact h
  refine ⟨prepare,z,F,_,output,same.trans user,Exec.seq build run,?_,?_,?_,reads,
    ownerLeft.trans (regs 0).2,ownerRight,accumulator,clear,maskEnd,modeEnd,restored,?_,done.2.2.1⟩
  · intro p tapeRate cleanTime
    have setup : q ≤ setupTime := by
      have scale : 0 < prime^layout.width*142080 := Nat.mul_pos (pow_pos Shared50ModularControl.prime_prime.pos _) (by decide)
      dsimp only [setupTime]
      rw [← Nat.add_mul_div_left _ _ scale]
      apply (Nat.le_div_iff_mul_le scale).mpr
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
    have scanBound := time p (le_max_left ..) (fun f => by cases f; exact le_max_right ..) first
    have suffix : (whole.R ((48 : Fin 66).castAdd K)).drop (64*64*data.H) = raw.R (bank 48) := by
      rw [show whole.R ((48 : Fin 66).castAdd K) = D.R (bank 48) from shared 48,matrix,
        ← length_matrixWords prime data.H (reduce M proj),List.drop_left]
    have leftBound : (privateTapes.map (fun i => 4*(whole.L i).length)).sum ≤ left :=
      List.sum_le_sum (fun i hi => Nat.mul_le_mul_left 4 (size ((placement i).castAdd 5)))
    have uniq : setupScratch.Nodup := by
      change (([58,61,66,67,68,69,71] : List (Fin 72)).map bank).Nodup
      exact List.Nodup.map bank.injective (by decide)
    have scanUniq : scanned.Nodup := List.Nodup.map (fun _ _ eq => placement.injective (Fin.castAdd_inj.mp eq))
      ((List.nodup_finRange _).filter _)
    have tailFits : tail.length ≤ (raw.R (bank 58)).length := by rw [source,List.length_append]; omega
    have occupied := inherited_le_stock u raw setupScratch scanned uniq scanUniq bank tail.length tapeRate tailFits
    simp only [scanned,List.map_map,Function.comp_def] at occupied
    change inherited+(left+tapeRate*((raw.R (bank 46)).length+(raw.R (bank 48)).length)) ≤ _ at occupied
    suffices exactTime : q+(k+(s+(t+n))) ≤ cleanTime+(inherited+(left+tapeRate*((raw.R (bank 46)).length+(raw.R (bank 48)).length))) by
      refine ⟨exactTime,?_⟩
      intro P priorBody prior initial n c arrival programPush bodyPush
      have stock := exec_stock visited arrival programPush bodyPush
      exact exactTime.trans (Nat.add_le_add_left (occupied.trans (Nat.mul_le_mul_left _ stock)) _)
    have combine (a b c d : ℕ) : a+b+(c+d) = a+c+(b+d) := by omega
    dsimp only [cleanTime]
    rw [combine]
    change _ ≤ setupTime+(_+_)
    rw [← ordinaryOwnerScanTime_inherited]
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
  · have stage (i : Fin 72) (hi : 58 ≤ i.val) : F.L (bank i) = [] ∧ F.R (bank i) = [] := by
      let k : Fin (66+K) := ⟨i.val,by have := i.isLt; omega⟩
      have above : i.val < (directoryMatrixTape room).val := by
        unfold directoryMatrixTape
        rw [directoryResidualBank_private room _ _ (by
          intro eq; have h := congrArg Fin.val eq; change 34 = rowSwapBlock.tapes+35 at h; omega)]
        change i.val < 66+(Record.size 127+34)
        omega
      have eq : placement k = k.castSucc := Fin.succAbove_of_castSucc_lt _ _ above
      have h := done.2.2.1 k hi
      change F.L ((placement k).castAdd 5) = [] ∧ F.R ((placement k).castAdd 5) = [] at h
      rw [eq] at h
      exact h
    have freeLeft (i) (mem : i ∈ setupScratch++scanned) : (F.L i).length = 0 := by
      rcases List.mem_append.mp mem with h | h
      · change i ∈ ([58,61,66,67,68,69,71] : List (Fin 72)).map bank at h
        obtain ⟨j,member,rfl⟩ := List.mem_map.mp h
        rw [(stage j ((by decide : ∀ j ∈ ([58,61,66,67,68,69,71] : List (Fin 72)), 58 ≤ j.val) j member)).1]
        rfl
      · obtain ⟨j,member,rfl⟩ := List.mem_map.mp h
        exact congrArg List.length (done.2.2.1 j (of_decide_eq_true (List.mem_filter.mp member).2)).1
    rw [← ordinaryInheritedBank_stock,Finset.sum_eq_zero (fun i hi => freeLeft i (List.mem_toFinset.mp hi)),Nat.zero_add,
        List.sum_toFinset _ (List.Nodup.map bank.injective (by decide : ([58,46,48] : List (Fin 72)).Nodup))]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,(stage 58 (by decide)).2,
      List.length_nil,Nat.zero_add,restored]

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
          root parent (by omega) (fits.trans (by omega)) (pool.trans (by omega)) (by omega) overhead budget localBody := by
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
