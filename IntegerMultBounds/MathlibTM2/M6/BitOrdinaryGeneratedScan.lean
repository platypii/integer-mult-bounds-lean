module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryGeneratedIncoming
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinarySelectors
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryCollect
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryReturn
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryHostedOutgoing
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryProjectedRead
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryPortReads
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryRowCost

/-! Generate incoming directory rows, transpose the batch, and restore bypassed rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open GoodForm FlatCoordinateLayout LabelTraversal Matrix M8.Exchange M8.ReversedExchange
open IntegerMultBounds.Swap.Shear HeadPivotLayout HeadWidthLayout CrossWeightLayout GoodChildLayout
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open RecursiveInterchangeLayout (Descriptor)
open IntegerMultBounds.Swap.Modular IntegerMultBounds.Swap.LowerTriangular Fast.Main

private theorem payloadWord_cast {V N : ℕ} (size : V = N) (word : Fin N → ZMod 2) :
    payloadWord (SparseRoleCircuit.encode ∘ word) =
      payloadWord (SparseRoleCircuit.encode ∘ (fun i : Fin V => word (i.cast size))) := by
  subst N
  rfl

private theorem replacedOwnerPayload {T V N : ℕ} (size : V = N) (port : Fin T)
    (word : Fin V → ZMod 2) (output : Fin N → ZMod 2) (B C : Stacks T prime)
    (old : RecordPayload port (fun _ => blank) 0 word B) (left : C.L port = B.L port)
    (right : C.R port = payloadWord (SparseRoleCircuit.encode ∘ output) ++ (B.R port).drop V) :
    RecordPayload port (fun _ => blank) 0 output C := by
  subst N
  have packed := payload_prefix_of_read word (fun _ => blank) 0 _ _ old
  simpa only [RecordPayload,sub_zero] using ownerWord_reads word output _ packed
    (by simpa only [RecordPayload,sub_zero] using old) left right

/-- Queue motion in a complete pass costs twelve steps per payload cell and
twelve per record, in addition to the row programs and four boundary steps. -/
theorem directoryScanTime_eq {ι : Type} (rs : List ι) (N : ℕ) (cost : ι → ℕ) :
    (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum+2*rs.length+2+(2*(rs.length*N)+2) =
      (rs.map cost).sum+12*(rs.length*N)+12*rs.length+4 := by
  have rows : (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum =
      (rs.map cost).sum+rs.length*(10*N+10) := by
    induction rs with
    | nil => simp
    | cons j rs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]
      omega
  rw [rows]
  ring

/-- The composed stage writes its complete packed output on the owner tape. -/
def DirectoryStageResult [M8.Machine.Net] {G U : Type} {T R N : ℕ} (host : G → Pr G T columnCapacity prime U)
    (program : Pr G T columnCapacity prime U) (a : HS T columnCapacity prime U) (A : Stacks T prime)
    (prior bound : ℕ) (port : Fin T) (tail : List (Fin (prime+4)))
    (effect : ℕ → (Fin N → ZMod 2) → Prop) : Prop :=
  ∃ z C n, ∃ output : Fin (R*N) → ZMod 2, z.user = a.user ∧ n ≤ bound ∧
    Exec host program (mk a A) (prior+n) (mk z C) ∧ (∀ j : Fin R, effect j (ownerRow rfl output j)) ∧
    RecordPayload port (fun _ => blank) 0 output C ∧
    C.R port = payloadWord (SparseRoleCircuit.encode ∘ output) ++ tail

/-- A complete interval-directory execution supplies the packed owner scan and
the address action at every routed port, with the same host run and charge. -/
theorem DirectoryStageResult.portReads [M8.Machine.Net] {G U : Type} {T R W w parents : ℕ}
    {host : G → Pr G T columnCapacity prime U} {program : Pr G T columnCapacity prime U}
    {a : HS T columnCapacity prime U} {A : Stacks T prime} {prior bound : ℕ} {port : Fin T}
    {tail : List (Fin (prime+4))} (interval : ℕ × ℕ) (weights : Fin 64 → ZMod (prime^(w+1)))
    (input : Fin (R*((prime^(w+1))^128*W)) → ZMod 2)
    (records : R = parents*(prime^(w+1))^(64*64)) (upper : interval.2 ≤ 63) :
    let M := prime^(w+1)
    let D : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    DirectoryStageResult host program a A prior bound port tail (R := R) (N := M^128*W)
      (fun j word => if LabelStock.live 64 (w+1) 1 j then ∀ x k,
        word (index ((projectorResidual finSumFinEquiv (reduce M D) weights (fun i => Ring.inverse (weights i))
          (physicalLabel 64 (w+1) j)).mulVec x) k) = ownerRow rfl input j (index x k)
        else ownerRow rfl input j = word) →
    ∃ z C n output, z.user = a.user ∧ n ≤ bound ∧ OwnerScan host program port output a A (prior+n) z C ∧
      PortReads R W parents interval weights input output ∧
      C.R port = payloadWord (SparseRoleCircuit.encode ∘ output) ++ tail := by
  intro M D stage
  obtain ⟨z,C,n,output,user,time,run,rows,read,packed⟩ := stage
  refine ⟨z,C,n,output,user,time,⟨run,?_⟩,PortReads.of_rows records upper rows,packed⟩
  intro j
  exact (show readAt blank (C.L port) (C.R port) j = _ from by simpa only [sub_zero] using read j).trans (encodedOwnerCell output j)

/-- The return program reuses the five owner registers and the two saved masks. -/
def directoryReturnPorts {T K : ℕ} (place : Fin (K+5) ↪ Fin T) (p : Fin 6 ↪ Fin T)
    (outside : ∀ k : Fin 6, 2 ≤ k → ∀ i, place i ≠ p k) : Fin 7 ↪ Fin T :=
  let regs : Fin 5 ↪ Fin T := (Fin.natAddEmb K).trans place
  ⟨![regs 0,regs 1,regs 3,regs 2,regs 4,p 2,p 3],by
    have apart (j : Fin 5) (k : Fin 6) (hk : 2 ≤ k) : regs j ≠ p k := outside k hk _
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | exact False.elim (regs.injective.ne (by decide) h) |
      exact False.elim (p.injective.ne (by decide) h) | exact False.elim (apart _ _ (by decide) h) |
      exact False.elim (apart _ _ (by decide) h.symm)⟩

/-- Execute the classified scan and retain both masks. On a complete owner tape, a framed
recursive transpose then returns the ordinary rows and restores each bypassed row. -/
theorem generatedIncomingDirectory_exec [M8.Machine.Net] {P U : Type} {r g d w common aux : ℕ}
    (v directory : Descriptor) :
    let W := directory.between*directory.afterD
    let m := r+g
    let hr : r ≤ m := Nat.le_add_right ..
    let K := common+24+31+aux
    let M := prime^(w+1)
    let H := M.size
    let J := W.size
    let N := M^(m+m)*W
    ∀ (dimension : m+m = d+1) (proj : Matrix (Fin m) (Fin m) ℚ) (_rank : proj.rank = r)
      (_idem : proj*proj = proj) (factor : Factorization Finset.univ Finset.univ proj)
      (_small : ∀ k ∈ factorizationDenominators factor, k < prime)
      (weights : Fin m → ZMod M) (_unit : ∀ i, IsUnit (weights i))
      (data : ScanData m d w W) (_binary : data.H = H) (_positive : 0 < W)
      (pool : (RingFormula.conjugationDepth m+1)*13 ≤ aux) (room : 58+(rowSwapBlock.tapes+35+1) ≤ K)
      (archiveRoom : Record.size d+(rowSwapBlock.tapes+35+2) ≤ K+1)
      (fits : (36+2*m+1+(RingFormula.conjugationDepth m+1)*13)+3 ≤ K+1)
      (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
      (localBody : P → Pr P (66+K) columnCapacity prime U) (localPush c : ℕ)
      (_bounded : ∀ f, mnProgPush (localBody f) ≤ localPush)
      (_placed : ∀ f, mnProgPush (embProg (directoryOrdinaryBank archiveRoom) id (localBody f)) ≤ c)
      (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4)))
      (input : ℕ → Fin N → ZMod 2) (B : ℕ)
      (_dirPositive : directory.Positive) (_shape : directory.beforeH = B*prime^(m*((w+1)*m)))
      (pairRoom : m*m+m*m ≤ K) (u : HS ((66+(K+1))+5) columnCapacity prime U) (S : Stacks ((66+(K+1))+5) prime),
    let full := ordinaryCaller (by omega : 58 ≤ K)
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let reduced := IntegerMultBounds.Swap.Modular.reduce M proj
    let localCaller := Fin.castAddEmb (n := 66) K
    let prog := incomingRowProgram (P := P) (U := U) (common := common) r g pool room
    let localTime := fun j => incomingRowTime U machine r g w W (prefixes j).length
    let privateTapes := (List.finRange (66+K)).filter (fun i => 58 ≤ i.val)
    let scanSlots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
    let scan := ((goodRecordScanPorts.trans scanSlots).trans (Fin.castAddEmb 8)).trans localCaller
    let skipRow : Pr P (66+K) columnCapacity prime U := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
    let goodRow := (prog.seq (clearWorkTapes privateTapes)).seq skipRow
    let push := max (mnProgPush prog) localPush
    let inv := fun i => Ring.inverse (weights i)
    let bad := fun j => fallbackBit proj.rank_le_height reduced (physicalLabel m (w+1) j)
    let budget := fun j => let cursor := 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)
                           if LabelStock.live m (w+1) 1 j then localTime j+(4*privateTapes.length+1+
                             privateTapes.length*(6*(push*localTime j)))+cursor else cursor
    let ordinaryEffect := fun j (out : Fin N → ZMod 2) =>
      let label := physicalLabel m (w+1) j
      let G := label*reduced*label⁻¹
      if LabelStock.live m (w+1) 1 j then ∃ minor : ∀ i (hi : i < r), IsUnit (lead (i+1) (lt_of_lt_of_le hi hr) G).det,
        ∃ before, IncomingRowEffect (w := w) (W := W) hr G minor weights inv (input j) before ∧
          ∀ i, out (i.cast (ordinaryChildVolume r g w W)) = before (ordinaryRecursivePosition r g w W i)
      else out = input j
    let body := fun f => embProg (directoryOrdinaryBank archiveRoom) id (localBody f)
    let length : N = M^m*(M^m*W) := by simp [N,pow_add,Nat.mul_assoc]
    let e := finSumFinEquiv.trans (finCongr dimension)
    let physical := data.physical e proj weights inv
    let φ := LabelRing.res prime (w+1) (by omega)
    let code := fun k => residualSchedule (A := prime) (projectorResidual finSumFinEquiv (reduce prime proj)
      (φ ∘ weights) (φ ∘ inv) (LabelStock.residue m (w+1) 1 k))
    let schedule : List ℕ → List (Fin (prime+4)) := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady (K := K) v proj w W data.H J weights prefixes archiveTail schedule
    let placement := directoryOrdinaryBank archiveRoom
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let live := LabelStock.live m (w+1) 1
    let rs := List.range data.records
    let bits := fun word : Fin N → ZMod 2 => payloadWord (SparseRoleCircuit.encode ∘ word)
    let outer := fun i : Fin (66+(K+1)) => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd (66+(K+1)) j
    let start := embStk outer S
    let inner := Fin.castAddEmb (n := 66) K
    let advance := dropWords (placement (inner 2)) (directoryMatrixTape archiveRoom) (placement (inner 59)) ((d+1)*(d+1))
    let good := (embProg placement id goodRow).seq advance
    let padding := (embProg placement id skipRow).seq advance
    let ordinaryTime := fun j => budget j + ((d+1)*(d+1)*(4*data.H+4)+1)
    let cost := fun j =>
      let C := physical.table (LabelStock.residue m (w+1) 1 j)
      let rows := classPivots C
      let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape archiveRoom)
      (if live j && bad j then exceptionalRecordTime U rows (negativeAnchor rows C) m w W data.H J scratch.length
        (max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d archiveRoom capacity)) c) (prefixes j).length else ordinaryTime j) +
        (if live j then 4 else 3)
    let projected := fun j (next : Fin N → ZMod 2) =>
      ∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) weights inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) =
        input j ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))
    let effect := fun j next => if live j && bad j then projected j next else ordinaryEffect j next
    let outProg := outgoingRowProgram (P := P) (U := U) (common := common) r g pool room
    let outPush := max (mnProgPush outProg) localPush
    let active : ℕ → Bool := fun j => live j && !bad j
    let dispatch : Pr P (66+K) columnCapacity prime U := ownerDispatch (inner 57) (inner 56) ((outProg.seq (clearWorkTapes privateTapes)).seq skipRow) skipRow skipRow
    let outLocal : Pr P ((66+K)+5) columnCapacity prime U := packedOwner (inner 24) (inner 57) dispatch
    let outCost := fun j => outgoingScanRowCost m w (prefixes j).length privateTapes.length outPush
      (outgoingRowTime U machine r g w W (prefixes j).length) (active j) (live j)
    start.R (directoryMatrixTape archiveRoom) = [] →
    let raw := embStk placement start
    let selectors := ordinarySelectorProgram localBody proj (φ ∘ weights) pairRoom
    let selectorBudget := (privateTapes.map fun i => 4*(raw.L i).length).sum +
      (140+30*(m*m)+6*privateTapes.length)*(data.records*N)
    data.records = LabelMask.records directory →
    (∀ i, 58 ≤ i.val → raw.R i = []) →
    DirectoryScanInput v proj w W data.H J weights prefixes archiveTail rs (fun i => raw.R (inner (i.castAdd 8))) →
    (raw.R (inner 29)).length = directory.beforeRows → (raw.R (inner 30)).length = directory.rows →
    (raw.R (inner 31)).length = directory.beforeH → raw.R (inner 50) = [] →
    raw.R (inner 57) = [] → raw.R (inner 56) = [] → raw.R (inner 54) = [] →
    S.R (reg 0) = rs.flatMap (bits ∘ input) ++ ownerTail → S.R (reg 1) = [] → (S.R (reg 2)).length = N →
    S.R (reg 3) = [] → S.R (reg 4) = [] → (∀ j, readAt blank (start.L (caller 24)) (start.R (caller 24)) j = blank) →
    let program := packedOwner (caller 24) (caller 57) (ownerDispatch (caller 57) (caller 56) good
      (directoryExceptionalProgram m d archiveRoom capacity) padding)
    let work := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape archiveRoom)
    let controls := embProg outer id (embProg placement id selectors)
    let prepare : Pr P (66+(K+1)) columnCapacity prime U := directoryQueueProgram archiveRoom fits e
    let smallBody := fun f => embProg outer id (body f)
    let suffix := (embProg outer id prepare).seq program
    let incoming := fun j (before : Fin N → ZMod 2) =>
      let label := physicalLabel m (w+1) j
      let G := label*reduced*label⁻¹
      ∃ minor : ∀ i (hi : i < r), IsUnit (lead (i+1) (lt_of_lt_of_le hi hr) G).det,
        IncomingRowEffect (w := w) (W := W) hr G minor weights inv (input j) before
    let pos := ordinaryRecursivePosition r g w W
    let size := ordinaryChildVolume r g w W
    let setupVolume := data.records*max (prefixes 0).length N
    let setupExtent := (1+m*m)*setupVolume + archiveTail.length + ((raw.R (inner 48)).drop (m*m*data.H)).length
    let initBudget := directoryQueueInitRate m d*setupExtent
    let setupBudget := fun p => initBudget + ((12*m*m+4+directoryMatrixRate m d)*setupVolume+4) +
      (4*work.length+1+work.length*(6*(p*initBudget)))
    let result := fun (elapsed : ℕ) (F : Stacks ((66+(K+1))+5) prime) => ∃ t n rows, elapsed = t+n ∧
      (∀ p, mnProgPush (directoryQueueInitProgram (P := P) (U := U) (Q := columnCapacity) archiveRoom fits) ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        t ≤ setupBudget p) ∧
      n ≤ (rs.map cost).sum+12*(rs.length*N)+12*rs.length+4 ∧
      (∀ j, readAt blank (F.L (outer (caller 24))) (F.R (outer (caller 24))) j = blank) ∧
      List.Forall₂ (fun j tape => ∃ physical,
        (if live j && !bad j then ∃ before, incoming j before ∧ physical = before ∘ pos
         else ∃ word, effect j word ∧ physical = fun i => word (i.cast size)) ∧
        tape = payloadWord (SparseRoleCircuit.encode ∘ physical)) rs rows ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = rows.flatten ++ ownerTail ∧ F.R (reg 1) = [] ∧
      (F.R (reg 2)).length = N ∧ F.R (reg 3) = [] ∧ F.R (reg 4) = [] ∧ ready (embStk placement (embStk outer F)) [] ∧
      (embStk outer F).R (directoryMatrixTape archiveRoom) = [] ∧
      (embStk outer F).R (caller 57) = [] ∧ (embStk outer F).R (caller 56) = []
    ∀ {G : Type} {T : ℕ} (place : Fin ((66+(K+1))+5) ↪ Fin T) (p : Fin 6 ↪ Fin T)
      (label : P → G) (host : G → Pr G T columnCapacity prime U) (_calls : ∀ f, host (label f) = embProg place label (smallBody f))
      (a : HS T columnCapacity prime U) (A : Stacks T prime),
    embDn place a = u → embStk place A = S →
    p 0 = place (outer (caller 57)) → p 1 = place (outer (caller 56)) →
    ∀ (outside : ∀ k : Fin 6, 2 ≤ k → ∀ i, place i ≠ p k), (∀ k : Fin 6, 2 ≤ k → A.R (p k) = []) →
    ∀ (replay : Fin 6 ↪ Fin T) (separate : ∀ i j, place i ≠ replay j)
      (_disjoint : ∀ i j, p i ≠ replay j), (∀ j, A.R (replay j) = []) →
    let localBank := placement.trans (Fin.castAddEmb 5)
    let slots := replaySlots.trans inner
    let copied := (Fin.castLEEmb (by decide : 4 ≤ 6)).trans replay
    let pairs := (List.finRange 4).map fun j => (place (localBank (slots j)),copied j)
    let snapshot : Pr G T columnCapacity prime U := Mult.PhaseCellToeplitz.copyWordHeaders (replay 4) (replay 5) pairs
    let copyTime := directoryReplayTime m w data.records (prefixes 0).length archiveTail.length
    let outBank := replayPlacement (localBank.trans place) slots copied (fun i j => separate _ _)
    let copy : Pr G T columnCapacity prime U := (bcopy (p 0) (p 2) (p 4) (p 5)).seq (bcopy (p 1) (p 3) (p 4) (p 5))
    let q := directoryReturnPorts place p outside
    let batch := ordinaryDirectoryChild directory r g w
    let V := RecursiveInterchangeLayout.volume prime batch
    let R := LabelMask.records directory
    let scan := (embProg place label controls).seq (snapshot.seq (copy.seq (embProg place label suffix)))
    ∃ (z : HS T columnCapacity prime U) (F : Stacks T prime) (s elapsed : ℕ) (mid : Stacks ((66+(K+1))+5) prime), z.user = a.user ∧ s ≤ selectorBudget ∧
      ready (embStk placement (embStk outer mid)) rs ∧
      (embStk outer mid).R (caller 48) = (embStk placement start).R (inner 48) ∧
      Exec host scan
        (mk a A) (s+(copyTime+(12*rs.length+12+elapsed))) (mk z F) ∧
      result elapsed (embStk place F) ∧ F.R (p 2) = rs.map (fun j => bitSymbol (live j)) ∧
      F.R (p 3) = rs.map (fun j => bitSymbol (bad j)) ∧
      (S.L (reg 0) = [] → ownerTail = [] → ∀ (f : G) (childBudget : ℕ),
        let D := {F with R := Function.update F.R (q 1) (F.R (q 0))}
        (∀ b : HS T columnCapacity prime U, b.user = z.user → ∀ x : Fin V → ZMod 2,
          RecordPayload (q 0) (fun _ => blank) 0 x D →
          ∃ y B k, y.user = b.user ∧ k ≤ childBudget ∧ Exec host (host f) (mk b D) k (mk y B) ∧
            RecordPayload (q 0) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
            ∀ i, i ≠ q 0 → B.L i = D.L i ∧ B.R i = D.R i) →
        let throughReturn : Pr G T columnCapacity prime U := scan.seq ((bcopy (q 0) (q 1) (q 2) (q 4)).seq ((.call f : Pr G T columnCapacity prime U).seq (directoryReturn q)))
        ∃ (y : HS T columnCapacity prime U) (B : Stacks T prime) (k : ℕ), ∃ out : Fin V → ZMod 2, y.user = a.user ∧ k ≤ childBudget+R*(16*N+14)+12 ∧
          (m = 64 → (prefixes 0).length ≤ N →
            copyTime+(12*rs.length+12)+k ≤ childBudget+72*(R*N)+6*archiveTail.length+49) ∧
          Exec host throughReturn
            (mk a A) ((s+(copyTime+(12*rs.length+12+elapsed)))+k) (mk y B) ∧
          RecordPayload (q 0) (fun _ => blank) 0 out B ∧
          (∀ j : Fin R, let row := ownerRow (ordinaryDirectoryChild_volume directory r g w) out j
            if live j && !bad j then ∃ before, incoming j before ∧
              row = ordinaryChildOutput (r := r) (g := g) (w := w) before ∘ pos
            else ∃ word, effect j word ∧ row = fun i => word (i.cast size)) ∧
          B.R (q 1) = [] ∧ B.R (q 2) = [] ∧ B.R (q 5) = [] ∧ B.R (q 6) = [] ∧
          B.R (q 0) = rs.flatMap (fun j => payloadWord (SparseRoleCircuit.encode ∘ ownerRow (ordinaryDirectoryChild_volume directory r g w) out j)) ++
            (B.R (q 0)).drop V ∧ (B.R (q 3)).length = N ∧ B.R (q 4) = [] ∧
          (∀ j, readAt blank (B.L (outBank (inner 24))) (B.R (outBank (inner 24))) j = blank) ∧
          DirectoryReady v proj w W data.H J weights prefixes archiveTail (fun _ => []) (embStk outBank B) rs ∧
          B.R (outBank (inner 57)) = rs.map (fun j => bitSymbol (live j)) ∧
          B.R (outBank (inner 56)) = rs.map (fun j => bitSymbol (bad j)) ∧
          (∀ i, i ∉ [q 0,q 1,q 2,q 5,q 6] → B.L i = F.L i ∧ B.R i = F.R i) ∧
          ∃ apart : ∀ (i : Fin (66+K)) (j : Fin 5), outBank i ≠ place (reg j),
          let regs := (Fin.natAddEmb (66+(K+1))).trans place
          let outPlace := outgoingOwnerPlacement outBank regs apart
          ∀ (dim : m = 64) (outLabel : P → G),
          (∀ f, host (outLabel f) = embProg outPlace outLabel (embProg (Fin.castAdd 5) id (localBody f))) →
          let inBill := (rs.map cost).sum+12*(rs.length*N)+12*rs.length+4
          let outBill := (rs.map outCost).sum+12*(rs.length*N)+12*rs.length+4
          let inRate := (incomingDirectoryTime_volume U machine r g d privateTapes.length push work.length
            (max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d archiveRoom capacity)) c) dim (by omega)).choose
          let outRate := (outgoingDirectoryTime_volume U machine r g privateTapes.length outPush dim).choose
          let weightedVolume := ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*((rs.length : ℝ)*N)
          ((prefixes 0).length ≤ N →
            (inBill : ℝ) ≤ inRate*weightedVolume+4 ∧ (outBill : ℝ) ≤ outRate*weightedVolume+4 ∧
            ∀ p, mnProgPush (directoryQueueInitProgram (P := P) (U := U) (Q := columnCapacity) archiveRoom fits) ≤ p →
              (∀ f, mnProgPush (body f) ≤ p) →
              ((s+(copyTime+(12*rs.length+12+elapsed))+k+outBill : ℕ) : ℝ) ≤
                ((selectorBudget+setupBudget p+childBudget+72*(R*N)+6*archiveTail.length+49 : ℕ) : ℝ) +
                  (inRate+outRate)*weightedVolume+8) ∧
          DirectoryStageResult (R := R) (N := N) host (throughReturn.seq (embProg outPlace outLabel outLocal)) a A
            ((s+(copyTime+(12*rs.length+12+elapsed)))+k)
            ((rs.map outCost).sum+12*(rs.length*N)+12*rs.length+4)
            (q 0) ((B.R (q 0)).drop V) (fun j word => if live j then projected j word else input j = word)) := by
  intro W m hr K M H J N dimension proj rank idem factor small weights unit data binary positive pool room
    archiveRoom fits capacity localBody localPush c bounded placed prefixes archiveTail ownerTail input B dirPositive shape pairRoom
    u S full machine reduced localCaller prog
    localTime privateTapes scanSlots scan skipRow goodRow push inv bad budget ordinaryEffect body length
    e physical φ code schedule ready placement caller live rs bits outer reg start inner advance good padding
    ordinaryTime cost projected effect outProg outPush active dispatch outLocal outCost initial raw selectors selectorBudget count free inputs beforeRows rowCount beforeH parents mask mode queueFree queue acc width saved tmp blankPort
  have adm : Admissible prime proj := by
    simpa using admissible_of_lt Shared50ModularControl.prime_prime
      (fun k (hk : k ∈ denominators proj) => small k (by simp [factorizationDenominators,hk])) 1
  let table := projectorResidual finSumFinEquiv (reduce prime proj) (φ ∘ weights) (φ ∘ inv)
  have inverse : φ ∘ inv = Ring.inverse ∘ (φ ∘ weights) := by
    funext i
    obtain ⟨a,ha⟩ := unit i
    change φ (Ring.inverse (weights i)) = Ring.inverse (φ (weights i))
    rw [← ha,Ring.inverse_unit]
    exact (Ring.inverse_unit (Units.map φ.toMonoidHom a)).symm
  obtain ⟨b,D,k,user,price,select,prepared,left,right,projector,cut,ls,bs⟩ :=
    (ordinarySelectors_exec localBody proj (reduce prime proj) table pairRoom).choose_spec
      (W := W) (H := data.H) (J := J) v weights (LabelProjector.residue_reduce (by omega) proj adm)
      directory dirPositive shape prefixes archiveTail (embDn placement (embDn outer u)) raw free
      (by simpa only [← count] using inputs) beforeRows rowCount beforeH parents mask mode queueFree
  have recordsPos : 0 < data.records := by
    rw [count]
    exact Nat.mul_pos (Nat.mul_pos dirPositive.1 dirPositive.2.1) dirPositive.2.2.1
  have radix : M ≤ N := by
    have h : M^1 ≤ M^(m+m) := Nat.pow_le_pow_right (pow_pos Shared50ModularControl.prime_prime.pos _) (by omega)
    exact (by simpa using h : M ≤ M^(m+m)).trans (Nat.le_mul_of_pos_right _ positive)
  have rowPos : 0 < N := (pow_pos Shared50ModularControl.prime_prime.pos _).trans_le radix
  have boxes : directory.beforeRows*directory.rows*B ≤ data.records := by
    rw [count]
    change _ ≤ directory.beforeRows*directory.rows*directory.beforeH
    rw [shape,← Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right _ (pow_pos Shared50ModularControl.prime_prime.pos _)
  have selectorPrice := maskSetup_volume_le m w data.records (directory.beforeRows*directory.rows*B)
    privateTapes.length (privateTapes.map fun i => 4*(raw.L i).length).sum (data.records*N)
    (radix.trans (Nat.le_mul_of_pos_left _ recordsPos)) (Nat.le_mul_of_pos_right _ rowPos) boxes
  have scanRun := classifiedDirectory_exec dimension v proj idem adm weights inv (fun i => Ring.mul_inverse_cancel _ (unit i))
    data (binary ▸ Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) positive archiveRoom fits capacity body c placed
    prefixes archiveTail bad budget ordinaryEffect length input localBody (fun _ => rfl) selectors goodRow skipRow
    selectorBudget ownerTail u S initial (by
      refine ⟨b,D,k,user,?_,?_,?_,left,right,projector,cut,?_,?_⟩
      · apply le_trans _ selectorPrice
        simpa only [List.length_range,count] using price
      · simpa only [selectors,ordinarySelectorProgram,table,inverse,Function.comp_assoc] using select
      · simpa only [count,rs] using prepared
      · simpa only [count,rs] using ls
      · simpa only [count,rs] using bs) queue acc width saved tmp blankPort (by
    intro j inside regular y A dir _ payload
    rw [binary] at dir
    obtain ⟨z,D,n,out,user,time,run,next,read,frame,action⟩ := generatedIncomingRow_exec (common := common)
      (r := r) (g := g) v proj rank weights unit prefixes archiveTail code j (rs.drop (j+1)) pool room localBody
      y A idem factor small dir (fun h => Bool.eq_false_iff.mpr (fun b => regular ⟨h,b⟩)) positive (input j) payload
      push (le_max_left ..) (fun f => (bounded f).trans (le_max_right ..))
    exact ⟨z,D,n,out,user,time,run,binary ▸ next,action,read,frame 40 (by decide),frame 57 (by decide),frame 56 (by decide)⟩)
  obtain ⟨_,_,_,_,_,s,b,mid,_,midUser,bound,control,lsMid,bsMid,_,resume,readyMid,projectorMid,_⟩ := scanRun
  intro program work controls prepare smallBody suffix incoming pos size setupVolume setupExtent initBudget setupBudget result G T place p label host calls a A hstate hstacks livePort badPort outside unused replay separate disjoint fresh localBank slots copied pairs snapshot copyTime outBank copy q batch V R scan
  obtain ⟨y,B,run,_,userY,project,frame⟩ := exec_emb place.injective calls control a hstate A hstacks
  have cell (i) : B.R (place i) = mid.R i := congrArg (fun D => Stacks.R D i) project
  have first : B.R (p 0) = rs.map (fun j => bitSymbol (live j)) := livePort ▸ (cell _).trans lsMid
  have second : B.R (p 1) = rs.map (fun j => bitSymbol (bad j)) := badPort ▸ (cell _).trans bsMid
  obtain ⟨a₁,A₁,copyUser,copyRun,project₁,retained,_,off⟩ := saveDirectoryReplay_exec host place
    (slots.trans localBank) replay separate y B (fun j => ((frame _ (fun i => separate i j)).2).trans (fresh j))
  have pOff (k : Fin 6) : A₁.R (p k) = B.R (p k) := off _ (fun j => (disjoint k _).symm)
  have timed : Exec host snapshot (mk y B) (copyTime) (mk a₁ A₁) := by
    refine Exec.cast copyRun ?_ rfl
    have measure := directoryReplayTime_eq (embStk localBank mid) readyMid
      recordsPos
      (by simpa only [localBank,embStk,Function.comp_apply,Function.Embedding.trans_apply,Fin.castAddEmb_apply,
        placement,directoryOrdinaryBank_caller,List.length_map,rs,List.length_range,outer,caller] using congrArg List.length lsMid)
      (by simpa only [localBank,embStk,Function.comp_apply,Function.Embedding.trans_apply,Fin.castAddEmb_apply,
        placement,directoryOrdinaryBank_caller,List.length_map,rs,List.length_range,outer,caller] using congrArg List.length bsMid)
    exact (congrArg (fun f => ((List.finRange 4).map f).sum+1)
      (funext (fun j => congrArg (fun xs => 6*List.length xs+6) (cell (localBank (slots j)))))).trans measure
  obtain ⟨z,F,t,user,continued,ok,ls,bs,untouched⟩ := saveMasksAndScan_exec smallBody place label host calls suffix p
    (fun i => ⟨outside 2 (by decide) i,outside 3 (by decide) i⟩) rs live bad a₁ A₁ ((pOff 0).trans first) ((pOff 1).trans second)
    (fun k hk => (pOff k).trans (((frame _ (outside k hk)).2).trans (unused k hk))) result (by
      intro a
      obtain ⟨z,F,k,n,rows,user,step,price,time,blankEnd,ordered,rest⟩ := resume a
      obtain ⟨init,queueBound⟩ := DirectoryReady.matrixSetup_volume data archiveRoom (embStk outer mid)
        readyMid binary radix recordsPos
      have widthEq := readyMid.2.1 0 (List.mem_range.mpr recordsPos)
      change ((embStk outer mid).R (placement (inner 47))).length = (prefixes 0).length at widthEq
      rw [show placement (inner 47) = caller 47 from directoryOrdinaryBank_caller archiveRoom 47] at widthEq
      change ((embStk outer mid).R ((47 : Fin 66).castAdd (K+1))).length = _ at widthEq
      have matrixEq : (embStk outer mid).R ((48 : Fin 66).castAdd (K+1)) = raw.R (inner 48) := projectorMid
      rw [widthEq,matrixEq] at init
      have setupBound (p) (hp) (hc) := (price p hp hc).trans (Nat.add_le_add (Nat.add_le_add init queueBound)
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left p init))) _))
      refine ⟨z,F,k+n,user,(project₁.trans project) ▸ step,k,n,rows,rfl,?_,time.trans_eq (directoryScanTime_eq rs N cost),blankEnd,?_,rest⟩
      · intro p hp hc
        simpa only [widthEq] using setupBound p hp hc
      · apply List.Forall₂.imp _ ordered
        intro j tape row
        obtain ⟨word,act,bytes⟩ := row
        refine ⟨fun i => word (i.cast size),?_,bytes.trans (payloadWord_cast size word)⟩
        split
        · next active =>
            obtain ⟨hl,hb⟩ := Bool.and_eq_true_iff.mp active
            have noBad : bad j = false := by simpa using hb
            simp only [noBad,Bool.and_false] at act
            change LabelStock.live m (w+1) 1 j = true at hl
            simp only [ordinaryEffect,hl,ite_true] at act
            obtain ⟨minor,before,action,packed⟩ := act
            exact ⟨before,⟨minor,action⟩,funext packed⟩
        · exact ⟨word,act,rfl⟩)
  have same : y.user = a.user := userY.trans (midUser.trans (congrArg HS.user hstate).symm)
  have scanned := Exec.seq run (Exec.seq timed continued)
  refine ⟨z,F,s,t,mid,user.trans (copyUser.trans same),bound,readyMid,projectorMid,scanned,ok,ls,bs,?_⟩
  intro left tail f childBudget D child
  obtain ⟨prepSteps,rowSteps,rows,elapsedEq,prepPaid,rowPaid,blankEnd,ordered,ownerLeft,ownerRight,accFree,finalWidth,clearSaved,clearTmp,finished,_⟩ := ok
  have queue : F.R (q 0) = rows.flatten := by
    change F.R (place (reg 0)) = rows.flatten
    exact ownerRight.trans (by rw [tail,List.append_nil])
  have maskList (flag : ℕ → Bool) : rs.map (fun j => bitSymbol (a := prime) (flag j)) =
      (List.finRange R).map (fun j => bitSymbol (flag j.val)) := by
    change (List.range data.records).map _ = _
    rw [count,← List.map_coe_finRange_eq_range,List.map_map]
    rfl
  let bypass := fun j (physical : Fin (RecursiveInterchangeLayout.volume prime (ordinaryChildDescriptor r g w W)) → ZMod 2) => ∃ word, effect j word ∧ physical = fun i => word (i.cast size)
  obtain ⟨y,B,k,out,huser,price,call,payload,action,cleared1,cleared2,cleared5,cleared6,frame⟩ :=
    scannedDirectoryCall_exec host f q directory r g w incoming bypass rows live bad z F childBudget
      (by simpa only [rs,count] using ordered) (ownerLeft.trans left) queue accFree clearSaved
      (finalWidth.trans size.symm) clearTmp (ls.trans (maskList live)) (bs.trans (maskList bad)) (by
        intro b hb x hx
        rw [← queue]
        exact child b hb x (by simpa only [D,queue] using hx))
  have offPorts (i : Fin T) (regs : ∀ k, place (reg k) ≠ i) (l : p 2 ≠ i) (b : p 3 ≠ i) :
      i ∉ [q 0,q 1,q 2,q 5,q 6] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨(regs 0).symm,(regs 1).symm,(regs 3).symm,l.symm,b.symm⟩
  have apart (i : Fin (66+K)) (j : Fin 5) : place (reg j) ≠ place (localBank i) := place.injective.ne (by
    intro eq
    have h := congrArg Fin.val eq
    change 66+(K+1)+j.val = (placement i).val at h
    have bound := (placement i).isLt
    omega)
  have keptBank (i : Fin (66+K)) := frame (place (localBank i)) (offPorts _ (apart i) (fun eq => outside 2 (by decide) _ eq.symm) (fun eq => outside 3 (by decide) _ eq.symm))
  have restored (j : Fin 4) : B.R (copied j) = mid.R (localBank (slots j)) := by
    have keep := frame (copied j) (offPorts _ (fun k => separate _ _) (disjoint 2 _) (disjoint 3 _))
    exact keep.2.trans ((untouched _ (fun i => separate i _) (disjoint 2 _).symm (disjoint 3 _).symm).trans
      ((retained j).trans (cell (localBank (slots j)))))
  have old : ready (embStk (localBank.trans place) B) [] := by
    let D := embStk (localBank.trans place) B
    let E := embStk placement (embStk outer (embStk place F))
    have leftEq : D.L = E.L := funext (fun i => (keptBank i).1)
    have rightEq : D.R = E.R := funext (fun i => (keptBank i).2)
    change DirectoryReady _ _ _ _ _ _ _ _ _ _ D []
    unfold DirectoryReady
    rw [leftEq,rightEq]
    exact finished
  have outgoing := outgoingReplay_ready (localBank.trans place) copied (fun i j => separate _ _)
    (embStk localBank mid) B live bad readyMid old rfl restored
    (by simpa only [localBank,Function.Embedding.trans_apply,embStk,Function.comp_apply,inner,caller,
      Fin.castAddEmb_apply,placement,directoryOrdinaryBank_caller] using lsMid)
    (by simpa only [localBank,Function.Embedding.trans_apply,embStk,Function.comp_apply,inner,caller,
      Fin.castAddEmb_apply,placement,directoryOrdinaryBank_caller] using bsMid)
  have blankReturned : ∀ j, readAt blank (B.L (outBank (inner 24))) (B.R (outBank (inner 24))) j = blank := by
    intro j
    have off : ∀ k, slots k ≠ inner 24 := fun k => inner.injective.ne ((by decide : ∀ k, replaySlots k ≠ 24) k)
    have unsaved : outBank (inner 24) = place (localBank (inner 24)) :=
      replayPlacement_off (localBank.trans place) slots copied (fun i j => separate _ _) _ off
    rw [unsaved]
    rw [(keptBank _).1,(keptBank _).2]
    have port : localBank (inner 24) = outer (caller 24) := congrArg outer (directoryOrdinaryBank_caller archiveRoom 24)
    rw [port]
    exact blankEnd j
  have returned : k ≤ childBudget+R*(16*N+14)+12 := by simpa only [ordinaryChildVolume] using price
  have charged (dim : m = 64) (fits : (prefixes 0).length ≤ N) :
      copyTime+(12*rs.length+12)+k ≤ childBudget+72*(R*N)+6*archiveTail.length+49 := by
    have extent : N = (prime^(w+1))^128*W := by rw [show N = M^(m+m)*W from rfl,dim]
    have records : 0 < data.records := by
      rw [count]
      exact Nat.mul_pos (Nat.mul_pos dirPositive.1 dirPositive.2.1) dirPositive.2.2.1
    have saved := directoryReplayTime_volume w data.records W (prefixes 0).length archiveTail.length
      records positive (extent ▸ fits)
    have copyBound : copyTime ≤ 30*(R*N)+6*archiveTail.length+25 := by
      simpa only [copyTime,dim,count,R,extent] using saved
    rw [show rs.length = R by simpa only [rs,List.length_range,R] using count]
    exact directoryReturnTime_volume (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive)
      copyBound returned
  intro throughReturn
  refine ⟨y,B,k,out,huser.trans (user.trans (copyUser.trans same)),returned,charged,
    Exec.seq scanned call,payload,action,cleared1,cleared2,cleared5,cleared6,
    by simpa only [rs,count] using returnedOwnerQueue (ordinaryDirectoryChild_volume directory r g w) out (q 0) B payload,
    (congrArg List.length (frame (q 3) (by simp [q.injective.eq_iff])).2).trans finalWidth,
    ((frame (q 4) (by simp [q.injective.eq_iff])).2).trans clearTmp,blankReturned,outgoing.1,outgoing.2.1,outgoing.2.2,frame,
    fun i j => replayPlacement_ne (localBank.trans place) slots copied (fun _ _ => separate _ _)
      (fun k => (apart k j).symm) (fun k => (separate _ _).symm) i,?_⟩
  intro regs outPlace dim outLabel outCalls inBill outBill inRate outRate weightedVolume
  constructor
  · intro width
    have extent : N = (prime^(w+1))^128*W := by rw [show N = M^(m+m)*W from rfl,dim]
    have widths := readyMid.2.1
    have fitAll (j) (hj : j ∈ rs) : (prefixes j).length ≤ (prime^(w+1))^128*W := by
      rw [← widths j hj,widths 0 (List.mem_range.mpr recordsPos)]
      exact extent ▸ width
    let piv := fun j => classPivots (physical.table (LabelStock.residue m (w+1) 1 j))
    let neg := fun j => negativeAnchor (piv j) (physical.table (LabelStock.residue m (w+1) 1 j))
    let rarePush := max (mnProgPush (directoryExceptionalCore (P := P) (U := U) d archiveRoom capacity)) c
    have incomingBill := (incomingDirectoryTime_volume U machine r g d privateTapes.length push work.length
      rarePush dim (by omega)).choose_spec w W positive rs (fun j => (prefixes j).length) live bad piv neg fitAll
    have inPrice : (inBill : ℝ) ≤ inRate*weightedVolume+4 := by
      have rowEq (j) : cost j = (if live j && bad j then
          exceptionalRecordTime U (piv j) (neg j) m w W M.size W.size work.length rarePush (prefixes j).length+4
        else outgoingScanRowCost m w (prefixes j).length privateTapes.length push (localTime j) (live j) (live j)+
          ((d+1)*(d+1)*(4*M.size+4)+1)) := by
        have hl : LabelStock.live m (w+1) 1 j = live j := rfl
        cases h : live j <;> cases b : bad j <;>
          simp only [cost,ordinaryTime,budget,outgoingScanRowCost,hl,h,b,binary,Bool.false_and,Bool.true_and,
            Bool.false_eq_true,ite_false,ite_true,piv,neg,rarePush,work,H,J] <;> omega
      dsimp only [weightedVolume]
      rw [← mul_assoc inRate]
      simpa only [inBill,inRate,← rowEq,localTime,m,M,extent] using incomingBill
    have priced := (outgoingDirectoryTime_volume U machine r g privateTapes.length outPush dim).choose_spec
      w W positive rs (fun j => (prefixes j).length) active live fitAll
    have outPrice : (outBill : ℝ) ≤ outRate*weightedVolume+4 := by
      simpa only [outBill,outRate,weightedVolume,mul_assoc,outCost,extent] using priced
    refine ⟨inPrice,outPrice,?_⟩
    intro p hp hc
    have overhead := charged dim width
    have setup := prepPaid p hp hc
    have physical : s+(copyTime+(12*rs.length+12+t))+k+outBill ≤
        (selectorBudget+setupBudget p+childBudget+72*(R*N)+6*archiveTail.length+49)+inBill+outBill := by
      change rowSteps ≤ inBill at rowPaid
      omega
    apply (Nat.cast_le.mpr physical).trans
    rw [Nat.cast_add,Nat.cast_add,add_mul]
    linarith only [inPrice,outPrice]
  let returned := ownerRow (ordinaryDirectoryChild_volume directory r g w) out
  obtain ⟨z,C,n,output,sameUser,time,run,rowAction,left,owner,_⟩ := hostedOutgoingScan_exec
    (common := common) v proj rank dim idem factor small weights unit positive prefixes archiveTail
    ((B.R (q 0)).drop V) R pool room localBody outBank regs _ outLabel host y B input returned outPush
    outCalls (le_max_left ..) (fun f => (bounded f).trans (le_max_right ..)) (by
      intro j inside l b
      change live j = true at l
      change bad j = false at b
      have hj : j < R := List.mem_range.mp inside
      obtain ⟨before,⟨minor,inc⟩,eqn⟩ := (by simpa [l,b] using action ⟨j,hj⟩ :
        ∃ before, incoming j before ∧ returned j = ordinaryChildOutput (r := r) (g := g) (w := w) before ∘ pos)
      exact ⟨minor,before,inc,eqn⟩)
    (by simpa only [rs,count,binary] using outgoing.1)
    (by simpa only [rs,count] using outgoing.2.1) (by simpa only [rs,count] using outgoing.2.2)
    (returnedOwnerQueue _ out (q 0) B payload) cleared1
    ((congrArg List.length (frame (q 3) (by simp [q.injective.eq_iff])).2).trans finalWidth) cleared2
    (((frame (q 4) (by simp [q.injective.eq_iff])).2).trans clearTmp) blankReturned effect (by
      intro j inactive
      change (live j && !bad j) = false at inactive
      simpa only [inactive,Bool.false_eq_true,ite_false] using action j)
  have volume : V = R*N := (ordinaryDirectoryChild_volume directory r g w).symm.trans (congrArg (R*·) size)
  refine ⟨z,C,n,output,sameUser.trans (huser.trans (user.trans (copyUser.trans same))),
    by rw [← directoryScanTime_eq]; simpa only [rs,count,R,outCost,outgoingScanRowCost,active,live,bad,reduced,machine,full,N,M,m,privateTapes,K] using time,Exec.seq (Exec.seq scanned call) run,?_,
    replacedOwnerPayload volume (q 0) out output B C payload left owner,owner⟩
  intro j
  have row := rowAction j
  change (if live j && !bad j then _ else effect j _) at row
  cases l : live j with
  | false =>
    simp only [l,Bool.false_and,Bool.false_eq_true,ite_false] at row ⊢
    have inactive : LabelStock.live m (w+1) 1 j = false := l
    exact (by simpa only [effect,l,Bool.false_and,Bool.false_eq_true,ite_false,ordinaryEffect,inactive] using row : _ = input j).symm
  | true =>
    simp only [l,ite_true,Bool.true_and] at row ⊢
    cases b : bad j with
    | true => simpa only [effect,l,b,Bool.not_true,Bool.true_and,Bool.false_eq_true,ite_false,ite_true] using row
    | false =>
      apply ordinaryProjectedRead dimension
      simpa only [b,Bool.not_false,ite_true] using row

end IntegerMultBounds.MathlibTM2.M6.BitNode
