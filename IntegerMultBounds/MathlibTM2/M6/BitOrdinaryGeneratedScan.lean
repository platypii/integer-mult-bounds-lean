module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryGeneratedIncoming

/-! Collect incoming physical rows for the shared ordinary transpose. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open GoodForm FlatCoordinateLayout LabelTraversal Matrix M8.Exchange M8.ReversedExchange
open IntegerMultBounds.Swap.Shear HeadPivotLayout HeadWidthLayout CrossWeightLayout GoodChildLayout
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

open RecursiveInterchangeLayout (Descriptor)
open IntegerMultBounds.Swap.Modular IntegerMultBounds.Swap.LowerTriangular Fast.Main

/-- Execute the classified incoming scan with generated ordinary rows, unchanged
padding and the physical exceptional projector. -/
theorem generatedIncomingDirectory_exec [M8.Machine.Net] {P U : Type} {r g d w W common aux : ℕ}
    (v : Descriptor) :
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
      (input : ℕ → Fin N → ZMod 2) (selectors : Pr P (66+K) columnCapacity prime U)
      (selectorBudget : ℕ) (u : HS ((66+(K+1))+5) columnCapacity prime U) (S : Stacks ((66+(K+1))+5) prime),
    let full := ordinaryCaller (by omega : 58 ≤ K)
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let reduced := IntegerMultBounds.Swap.Modular.reduce M proj
    let localCaller := Fin.castAddEmb (n := 66) K
    let is := ordinaryChildPackSchedule r g
    let prog := incomingRowProgram (P := P) (U := U) (common := common) r g pool room
    let localTime := fun j => ordinarySetupTime m r w H (prefixes j).length +
      (1+goodIncomingTime (A := prime) (U := U) Empty.elim machine prime w W H J r hr +
      (1+((is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim (m+m) i (i+1) w W H J)).sum+1)))
    let privateTapes := (List.finRange (66+K)).filter (fun i => 58 ≤ i.val)
    let scanSlots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
    let scan := ((goodRecordScanPorts.trans scanSlots).trans (Fin.castAddEmb 8)).trans localCaller
    let skipRow := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
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
    let ready := DirectoryReady v proj w W data.H J weights prefixes archiveTail schedule
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
    let effect := fun j (next : Fin N → ZMod 2) => if live j && bad j then
      ∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) weights inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) =
        input j ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))
      else ordinaryEffect j next
    start.R (directoryMatrixTape archiveRoom) = [] →
    (∃ y D t, y.user = u.user ∧ t ≤ selectorBudget ∧
      Exec localBody selectors (mk (embDn placement (embDn outer u)) (embStk placement start)) t (mk y D) ∧
      ready D rs ∧ D.L (inner 24) = (embStk placement start).L (inner 24) ∧
      D.R (inner 24) = (embStk placement start).R (inner 24) ∧
      D.R (inner 48) = (embStk placement start).R (inner 48) ∧ D.R (inner 40) = (embStk placement start).R (inner 40) ∧
      D.R (inner 57) = rs.map (fun j => bitSymbol (live j)) ∧ D.R (inner 56) = rs.map (fun j => bitSymbol (bad j))) →
    S.R (reg 0) = rs.flatMap (bits ∘ input) ++ ownerTail → S.R (reg 1) = [] → (S.R (reg 2)).length = N →
    S.R (reg 3) = [] → S.R (reg 4) = [] → (∀ j, readAt blank (start.L (caller 24)) (start.R (caller 24)) j = blank) →
    let program := packedOwner (caller 24) (caller 57) (ownerDispatch (caller 57) (caller 56) good
      (directoryExceptionalProgram m d archiveRoom capacity) padding)
    let work := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape archiveRoom)
    let controls := embProg outer id (embProg placement id selectors)
    let prepare : Pr P (66+(K+1)) columnCapacity prime U := directoryQueueProgram archiveRoom fits e
    ∃ z F t n rows s midUser mid, z.user = u.user ∧ s ≤ selectorBudget ∧
      Exec (fun f => embProg outer id (body f)) controls (mk u S) s (mk midUser mid) ∧
      ready (embStk placement (embStk outer mid)) rs ∧
      (embStk outer mid).R (caller 48) = (embStk placement start).R (inner 48) ∧
      let initTime := directoryQueueInitTime m d w data.H data.records (embStk outer mid)
      let queueTime := directoryMatrixQueueTime m d w data.H data.records ((embStk outer mid).R (caller 47)).length

      (∀ p, mnProgPush (directoryQueueInitProgram (P := P) (U := U) (Q := columnCapacity) archiveRoom fits) ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        t ≤ initTime + queueTime + (4*work.length+1+work.length*(6*(p*initTime)))) ∧
      n ≤ (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum + 2*rs.length+2 + (2*(rs.length*N)+2) ∧
      Exec (fun f => embProg outer id (body f)) (controls.seq ((embProg outer id prepare).seq program)) (mk u S) (s+(t+n)) (mk z F) ∧
      List.Forall₂ (fun j out => ∃ word, effect j word ∧ out = bits word) rs rows ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = rows.flatten ++ ownerTail ∧ F.R (reg 1) = [] ∧ ready (embStk placement (embStk outer F)) [] ∧
      (embStk outer F).R (directoryMatrixTape archiveRoom) = [] ∧
      (embStk outer F).R (caller 57) = [] ∧ (embStk outer F).R (caller 56) = [] := by
  intro m hr K M H J N dimension proj rank idem factor small weights unit data binary positive pool room
    archiveRoom fits capacity localBody localPush c bounded placed prefixes archiveTail ownerTail input selectors
    selectorBudget u S full machine reduced localCaller is prog
    localTime privateTapes scanSlots scan skipRow goodRow push inv bad budget ordinaryEffect body length
    e physical φ code schedule ready placement caller live rs bits outer reg start inner advance good padding
    ordinaryTime cost effect initial selectorRun queue acc width saved tmp blankPort
  have adm : Admissible prime proj := by
    simpa using admissible_of_lt Shared50ModularControl.prime_prime
      (fun k (hk : k ∈ denominators proj) => small k (by simp [factorizationDenominators,hk])) 1
  apply classifiedDirectory_exec dimension v proj idem adm weights inv (fun i => Ring.mul_inverse_cancel _ (unit i))
    data (binary ▸ Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) positive archiveRoom fits capacity body c placed
    prefixes archiveTail bad budget ordinaryEffect length input localBody (fun _ => rfl) selectors goodRow skipRow
    selectorBudget ownerTail u S initial selectorRun queue acc width saved tmp blankPort
  intro j inside regular y A dir _ payload
  rw [binary] at dir
  obtain ⟨z,D,n,out,user,time,run,next,read,frame,action⟩ := generatedIncomingRow_exec (common := common)
    (r := r) (g := g) v proj rank weights unit prefixes archiveTail code j (rs.drop (j+1)) pool room localBody
    y A idem factor small dir (fun h => Bool.eq_false_iff.mpr (fun b => regular ⟨h,b⟩)) positive (input j) payload
    push (le_max_left ..) (fun f => (bounded f).trans (le_max_right ..))
  exact ⟨z,D,n,out,user,time,run,binary ▸ next,action,read,frame 40 (by decide),frame 57 (by decide),frame 56 (by decide)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
