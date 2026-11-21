module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryGeneratedIncoming
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinarySelectors
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryCollect

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
      (input : ℕ → Fin N → ZMod 2) (directory : Descriptor) (B : ℕ)
      (_dirPositive : directory.Positive) (_shape : directory.beforeH = B*prime^(m*((w+1)*m)))
      (pairRoom : m*m+m*m ≤ K) (u : HS ((66+(K+1))+5) columnCapacity prime U) (S : Stacks ((66+(K+1))+5) prime),
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
    let effect := fun j (next : Fin N → ZMod 2) => if live j && bad j then
      ∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) weights inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) =
        input j ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))
      else ordinaryEffect j next
    start.R (directoryMatrixTape archiveRoom) = [] →
    let raw := embStk placement start
    let selectors := ordinarySelectorProgram localBody proj (φ ∘ weights) pairRoom
    let selectorBudget := (26*prime^w+4) +
      ((44*data.records+13*(w+1)+16)+3*((6+10*(m*m))*data.records+4)+(2*(directory.beforeRows*directory.rows*B)+2)) +
      ((privateTapes.map fun i => 4*(raw.L i).length).sum+privateTapes.length*(2*prime^w+4)+1)
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
    let result := fun (mid : Stacks ((66+(K+1))+5) prime) (elapsed : ℕ) (F : Stacks ((66+(K+1))+5) prime) => ∃ t n rows, elapsed = t+n ∧
      let initTime := directoryQueueInitTime m d w data.H data.records (embStk outer mid)
      let queueTime := directoryMatrixQueueTime m d w data.H data.records ((embStk outer mid).R (caller 47)).length

      (∀ p, mnProgPush (directoryQueueInitProgram (P := P) (U := U) (Q := columnCapacity) archiveRoom fits) ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        t ≤ initTime + queueTime + (4*work.length+1+work.length*(6*(p*initTime)))) ∧
      n ≤ (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum + 2*rs.length+2 + (2*(rs.length*N)+2) ∧
      List.Forall₂ (fun j out => ∃ word, effect j word ∧ out = bits word) rs rows ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = rows.flatten ++ ownerTail ∧ F.R (reg 1) = [] ∧ ready (embStk placement (embStk outer F)) [] ∧
      (embStk outer F).R (directoryMatrixTape archiveRoom) = [] ∧
      (embStk outer F).R (caller 57) = [] ∧ (embStk outer F).R (caller 56) = []
    ∀ {T : ℕ} (place : Fin ((66+(K+1))+5) ↪ Fin T) (p : Fin 6 ↪ Fin T)
      (host : P → Pr P T columnCapacity prime U) (_calls : ∀ f, host f = embProg place id (smallBody f))
      (a : HS T columnCapacity prime U) (A : Stacks T prime),
    embDn place a = u → embStk place A = S →
    p 0 = place (outer (caller 57)) → p 1 = place (outer (caller 56)) →
    (∀ k : Fin 6, 2 ≤ k → ∀ i, place i ≠ p k) → (∀ k : Fin 6, 2 ≤ k → A.R (p k) = []) →
    let copy : Pr P T columnCapacity prime U := (bcopy (p 0) (p 2) (p 4) (p 5)).seq (bcopy (p 1) (p 3) (p 4) (p 5))
    ∃ (z : HS T columnCapacity prime U) (F : Stacks T prime) (s elapsed : ℕ) (mid : Stacks ((66+(K+1))+5) prime), z.user = a.user ∧ s ≤ selectorBudget ∧
      ready (embStk placement (embStk outer mid)) rs ∧
      (embStk outer mid).R (caller 48) = (embStk placement start).R (inner 48) ∧
      Exec host ((embProg place id controls).seq (copy.seq (embProg place id suffix)))
        (mk a A) (Nat.add s (Nat.add (Nat.add (Nat.mul 12 rs.length) 12) elapsed)) (mk z F) ∧
      result mid elapsed (embStk place F) ∧ F.R (p 2) = rs.map (fun j => bitSymbol (live j)) ∧
      F.R (p 3) = rs.map (fun j => bitSymbol (bad j)) := by
  intro m hr K M H J N dimension proj rank idem factor small weights unit data binary positive pool room
    archiveRoom fits capacity localBody localPush c bounded placed prefixes archiveTail ownerTail input directory B dirPositive shape pairRoom
    u S full machine reduced localCaller is prog
    localTime privateTapes scanSlots scan skipRow goodRow push inv bad budget ordinaryEffect body length
    e physical φ code schedule ready placement caller live rs bits outer reg start inner advance good padding
    ordinaryTime cost effect initial raw selectors selectorBudget count free inputs beforeRows rowCount beforeH parents mask mode queueFree queue acc width saved tmp blankPort
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
  have scanRun := classifiedDirectory_exec dimension v proj idem adm weights inv (fun i => Ring.mul_inverse_cancel _ (unit i))
    data (binary ▸ Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) positive archiveRoom fits capacity body c placed
    prefixes archiveTail bad budget ordinaryEffect length input localBody (fun _ => rfl) selectors goodRow skipRow
    selectorBudget ownerTail u S initial (by
      refine ⟨b,D,k,user,?_,?_,?_,left,right,projector,cut,?_,?_⟩
      · simpa only [selectorBudget,List.length_range,count] using price
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
  intro program work controls prepare smallBody suffix result T place p host calls a A hstate hstacks livePort badPort outside unused copy
  obtain ⟨y,B,run,_,userY,project,frame⟩ := exec_emb place.injective calls control a hstate A hstacks
  have cell (i) : B.R (place i) = mid.R i := congrArg (fun D => Stacks.R D i) project
  have first : B.R (p 0) = rs.map (fun j => bitSymbol (live j)) := livePort ▸ (cell _).trans lsMid
  have second : B.R (p 1) = rs.map (fun j => bitSymbol (bad j)) := badPort ▸ (cell _).trans bsMid
  obtain ⟨z,F,t,user,continued,ok,ls,bs⟩ := saveMasksAndScan_exec smallBody place host calls suffix p
    (fun i => ⟨outside 2 (by decide) i,outside 3 (by decide) i⟩) rs live bad y B first second
    (fun k hk => ((frame _ (outside k hk)).2).trans (unused k hk)) (result mid) (by
      intro a
      obtain ⟨z,F,k,n,rows,user,step,price,time,ordered,rest⟩ := resume a
      exact ⟨z,F,k+n,user,project ▸ step,k,n,rows,rfl,price,time,ordered,rest⟩)
  have same : y.user = a.user := userY.trans (midUser.trans (congrArg HS.user hstate).symm)
  exact ⟨z,F,s,t,mid,user.trans same,bound,readyMid,projectorMid,Exec.seq run continued,ok,ls,bs⟩


end IntegerMultBounds.MathlibTM2.M6.BitNode
