module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinarySelectors
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryEntry

/-! The classified owner scan with the live stopped adapter and identity padding. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor)
open IntegerMultBounds.MathlibTM2.Stack Host Cover Cover.Fallback M8.RevMachine
open IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.Swap.Modular Matrix
open LabelTraversal FlatCoordinateLayout M8.Exchange M8.ReversedExchange IntegerMultBounds.Swap.Shear

/-- The split banks of an ordinary row and the residual matrix use the same packed address. -/
private theorem ordinaryProjectedRead {m n M W : ℕ} [NeZero M] (dimension : m+m = n)
    (P g : Matrix (Fin m) (Fin m) (ZMod M)) (parent inv : Fin m → ZMod M)
    (input output : Fin (M^(m+m)*W) → ZMod 2)
    (read : ∀ x k,
      let y := transform (diagonal parent) 1 (revExchangeOf (rev m) (g*P*g⁻¹) (transform (diagonal inv) 1 x))
      output (index (Fin.append y.1 y.2) k) = input (index (Fin.append x.1 x.2) k)) :
    let e := finSumFinEquiv.trans (finCongr dimension)
    ∀ x (k : Fin W), output ((index ((projectorResidual e P parent inv g).mulVec x) k).cast (by rw [dimension])) =
      input ((index x k).cast (by rw [dimension])) := by
  subst n
  intro e x k
  let banks := (x ∘ e ∘ Sum.inl, x ∘ e ∘ Sum.inr)
  let y := transform (diagonal parent) 1 (revExchangeOf (rev m) (g*P*g⁻¹) (transform (diagonal inv) 1 banks))
  have append (u v : Fin m → ZMod M) : Sum.elim u v ∘ e.symm = Fin.append u v := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [e]
    | right i =>
      change Sum.elim u v (finSumFinEquiv.symm (Fin.natAdd m i)) = Fin.append u v (Fin.natAdd m i)
      simp only [finSumFinEquiv_symm_apply_natAdd,Sum.elim_inr,Fin.append_right]
  have split : x ∘ e = Sum.elim banks.1 banks.2 := by funext i; cases i <;> rfl
  have joined : Fin.append banks.1 banks.2 = x := by
    rw [← append,← split]; funext i; simp
  have projected : (projectorResidual e P parent inv g).mulVec x = Fin.append y.1 y.2 := by
    change (residual _ _ _ _).submatrix e.symm e.symm *ᵥ x = _
    rw [submatrix_mulVec_equiv,show x ∘ e.symm.symm = Sum.elim banks.1 banks.2 from split,residual_mulVec]
    exact append _ _
  rw [projected]
  change output (index (Fin.append y.1 y.2) k) = input (index x k)
  calc
    _ = input (index (Fin.append banks.1 banks.2) k) := read banks k
    _ = _ := congrArg (fun u => input (index u k)) joined

def ClassifiedOrdinaryScan [M8.Machine.Net] {a d common work w W J : ℕ} {U : Type}
    (v : Descriptor) (proj : Matrix (Fin (a+1)) (Fin (a+1)) ℚ)
    (dimension : (a+1)+(a+1) = d+1)
    (parent : Fin (a+1) → ZMod (prime^(w+1)))
    (data : ScanData (a+1) d w W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*(a+1)+1+(RingFormula.conjugationDepth (a+1)+1)*13)+3 ≤ (common+24+31+work)+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (pool : (RingFormula.conjugationDepth (a+1)+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (cap : 217 ≤ columnCapacity) (overhead childBudget : ℕ)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4)))
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U) : Prop :=
    let m := a+1
    let K := common+24+31+work
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let N := M^(m+m)*W
    let inv := fun i => Ring.inverse (parent i)
    let bad := fun j => fallbackBit proj.rank_le_height (reduce M proj) (physicalLabel m (w+1) j)
    let length : N = M^m*(M^m*W) := by simp [N,pow_add,Nat.mul_assoc]
    ∀ (word : Fin (data.records*N) → ZMod 2)
      (directory : Descriptor) (B : ℕ)
      (u : HS ((66+(K+1))+5) columnCapacity prime U) (S : Stacks ((66+(K+1))+5) prime),
    let input := ownerRow (R := data.records) (N := N) rfl word
    let body := fun f => embProg (directoryOrdinaryBank room) id (localBody f)
    let c := mnProgPush (body ())
    let core := ordinaryRowCore (U := U) cap m proj.rank proj.rank_le_height pool space
    let ports := ordinaryCursorPorts.trans (Fin.castAddEmb (n := 66) K)
    let skipRow := readWithSuccessorClock (ports 1) (advanceDirectory m ports)
    let step := core.seq skipRow
    let scratch := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let goodRow := step.seq (clearWorkTapes scratch)
    let push := max (mnProgPush step) (mnProgPush (localBody ()))
    let budget := fun j =>
      let pad := 1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)
      let elapsed := ordinaryRowTime m proj.rank w W data.H (prefixes j).length overhead childBudget + pad
      if LabelStock.live m (w+1) 1 j then elapsed+(4*scratch.length+1+scratch.length*(6*(push*elapsed))) else pad
    let ordinaryEffect := fun j (out : Fin N → ZMod 2) =>
      let g := physicalLabel m (w+1) j
      if LabelStock.live m (w+1) 1 j then ∀ x k,
        let y := transform (diagonal parent) 1 (revExchangeOf (rev m) (g*reduce M proj*g⁻¹) (transform (diagonal inv) 1 x))
        out (index (Fin.append y.1 y.2) k) = input j (index (Fin.append x.1 x.2) k)
      else input j = out
    let e := finSumFinEquiv.trans (finCongr dimension)
    let physical := data.physical e proj parent inv
    let φ := LabelRing.res prime (w+1) (by omega)
    let code := fun k => residualSchedule (A := prime) (projectorResidual finSumFinEquiv (reduce prime proj)
      (φ ∘ parent) (φ ∘ inv) (LabelStock.residue m (w+1) 1 k))
    let schedule := fun (xs : List ℕ) => xs.flatMap fun k => if bad k then code k else []
    let ready := DirectoryReady v proj w W data.H J parent prefixes archiveTail schedule
    let placement := directoryOrdinaryBank room
    let caller := Fin.castAddEmb (n := 66) (K+1)
    let live := LabelStock.live m (w+1) 1
    let rs := List.range data.records
    let pending := fun j => rs.drop j
    let bank := fun i : Fin (66+(K+1)) => i.castAdd 5
    let reg := fun j : Fin 5 => Fin.natAdd (66+(K+1)) j
    let start := embStk bank S
    let inner := Fin.castAddEmb (n := 66) K
    let advance := dropWords (placement (inner 2)) (directoryMatrixTape room) (placement (inner 59)) ((d+1)*(d+1))
    let good := (embProg placement id goodRow).seq advance
    let padding := (embProg placement id skipRow).seq advance
    let ordinaryTime := fun j => budget j + ((d+1)*(d+1)*(4*data.H+4)+1)
    let cost := fun j =>
      let C := physical.table (LabelStock.residue m (w+1) 1 j)
      let rows := classPivots C
      let scratch := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
      (if live j && bad j then exceptionalRecordTime U rows (negativeAnchor rows C) m w W data.H J scratch.length
        (max (mnProgPush (directoryExceptionalCore (P := Unit) (U := U) d room capacity)) c) (prefixes j).length else ordinaryTime j) +
        (if live j then 4 else 3)
    let effect := fun j (next : Fin N → ZMod 2) => if live j then
      ∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) =
        input j ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))
      else input j = next
    start.R (directoryMatrixTape room) = [] →
    let raw := embStk placement start
    let privateTapes := (List.finRange (66+K)).filter fun i => 58 ≤ i.val
    let left := (privateTapes.map fun i => 4*(raw.L i).length).sum
    let selectorBudget := left+(140+30*(m*m)+6*privateTapes.length)*(data.records*N)
    directory.Positive → directory.beforeH = B*prime^(m*((w+1)*m)) →
    data.records = LabelMask.records directory → m*m+m*m ≤ K →
    (∀ i, 58 ≤ i.val → raw.R i = []) →
    DirectoryScanInput v proj w W data.H J parent prefixes archiveTail rs (fun i => raw.R (inner (i.castAdd 8))) →
    (raw.R (inner 29)).length = directory.beforeRows → (raw.R (inner 30)).length = directory.rows →
    (raw.R (inner 31)).length = directory.beforeH → raw.R (inner 50) = [] →
    raw.R (inner 57) = [] → raw.R (inner 56) = [] → raw.R (inner 54) = [] →
    S.R (reg 0) = payloadWord (SparseRoleCircuit.encode ∘ word) ++ ownerTail →
    (∀ j, readAt blank (S.L (reg 0)) (S.R (reg 0)) j = RadixToBinary.binaryEncoding.encode
      (putWord (fun _ => blank) 0 ((List.ofFn word).map SparseRoleCircuit.encode) j)) → S.R (reg 1) = [] → S.R (reg 2) = [] →
    S.R (reg 3) = [] → S.R (reg 4) = [] → (∀ j, readAt blank (start.L (caller 24)) (start.R (caller 24)) j = blank) →
    let program := packedOwner (caller 24) (caller 57) (ownerDispatch (caller 57) (caller 56) good
      (directoryExceptionalProgram m d room capacity) padding)
    let work := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    ∃ selectors : Pr Unit (66+K) columnCapacity prime U,
    let controls := embProg bank id (embProg placement id selectors)
    ∃ prepare z F t n output k s midUser mid,
      k ≤ dimensionTime data.H J (d+1)+6*N+13*((d+1)*data.H+J)+8 ∧ z.user = u.user ∧ s ≤ selectorBudget ∧
      Exec (fun f => embProg bank id (body f)) ((payloadCountProgram (ownerCountPorts (K+1)) (d+1)).seq controls) (mk u S) (k+s) (mk midUser mid) ∧
      ready (embStk placement (embStk bank mid)) rs ∧
      (embStk bank mid).R (caller 48) = (embStk placement start).R (inner 48) ∧
      let initTime := directoryQueueInitTime m d w data.H data.records (embStk bank mid)
      let queueTime := directoryMatrixQueueTime m d w data.H data.records ((embStk bank mid).R (caller 47)).length

      (∀ p, mnProgPush prepare ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        t ≤ initTime + queueTime + (4*work.length+1+work.length*(6*(p*initTime)))) ∧
      n ≤ (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum + 2*rs.length+2 + (2*(rs.length*N)+2) ∧
      Exec (fun f => embProg bank id (body f)) ((payloadCountProgram (ownerCountPorts (K+1)) (d+1)).seq (controls.seq ((embProg bank id prepare).seq program))) (mk u S) (k+(s+(t+n))) (mk z F) ∧
      (∀ j : Fin data.records, effect j (ownerRow (R := data.records) (N := N) rfl output j)) ∧
      (∀ j, readAt blank (F.L (reg 0)) (F.R (reg 0)) j = RadixToBinary.binaryEncoding.encode
        (putWord (fun _ => blank) 0 ((List.ofFn output).map SparseRoleCircuit.encode) j)) ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = payloadWord (SparseRoleCircuit.encode ∘ output) ++ ownerTail ∧ F.R (reg 1) = [] ∧ ready (embStk placement (embStk bank F)) [] ∧
      (embStk bank F).R (directoryMatrixTape room) = [] ∧
      (embStk bank F).R (caller 57) = [] ∧ (embStk bank F).R (caller 56) = []

theorem classifiedOrdinaryDirectory_exec [M8.Machine.Net] {a d common work w W J : ℕ} {U : Type}
    (v : Descriptor) (proj : Matrix (Fin (a+1)) (Fin (a+1)) ℚ)
    (dimension : (a+1)+(a+1) = d+1) (idem : proj*proj = proj) (adm : Admissible prime proj)
    (parent : Fin (a+1) → ZMod (prime^(w+1))) (unit : ∀ i, IsUnit (parent i))
    (data : ScanData (a+1) d w W) (hm : prime^(w+1) < 2^data.H) (hw : W < 2^J) (positive : 0 < W)
    (room : Record.size d+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*(a+1)+1+(RingFormula.conjugationDepth (a+1)+1)*13)+3 ≤ (common+24+31+work)+1)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ columnCapacity)
    (pool : (RingFormula.conjugationDepth (a+1)+1)*13 ≤ work) (space : 58 ≤ common+24+31+work)
    (cap : 217 ≤ columnCapacity) (overhead childBudget : ℕ)
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4))) :
    let m := a+1
    let K := common+24+31+work
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let N := M^(m+m)*W
    let inv := fun i => Ring.inverse (parent i)
    let bad := fun j => fallbackBit proj.rank_le_height (reduce M proj) (physicalLabel m (w+1) j)
    let length : N = M^m*(M^m*W) := by simp [N,pow_add,Nat.mul_assoc]
    ∀ localBody : Unit → Pr Unit (66+K) columnCapacity prime U,
    (∀ j, LabelStock.live m (w+1) 1 j = true → bad j = false →
      let g := physicalLabel m (w+1) j
      ∀ minor, OrdinaryRecordExec (W := W) (H := data.H) (J := J) cap proj.rank_le_height
        (ordinaryCaller space) localBody overhead childBudget (g*reduce M proj*g⁻¹) minor parent) →
    ClassifiedOrdinaryScan (J := J) v proj dimension parent data room fits capacity pool space cap overhead childBudget
      prefixes archiveTail ownerTail localBody := by
  intro m K M N inv bad length localBody installed
  unfold ClassifiedOrdinaryScan
  intro _ _ _ _ _ actualBad _ word directory B u S input body c core ports skipRow step scratch goodRow push budget ordinaryEffect
  intro e physical φ code schedule ready placement caller live rs pending bank reg start inner advance good padding ordinaryTime cost effect
    matrix raw privateTapes left selectorBudget dirPositive shape count pairRoom free inputs beforeRows rows beforeH parents mask mode queueFree
    owner reads accumulator width saved tmp empty
  have recordsPos : 0 < data.records := by
    rw [count]; exact Nat.mul_pos (Nat.mul_pos dirPositive.1 dirPositive.2.1) dirPositive.2.2.1
  have radixPos : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have radix : M ≤ N := by
    have bound : M^1 ≤ M^(m+m) := Nat.pow_le_pow_right radixPos (by dsimp [m]; omega)
    exact (by simpa using bound : M ≤ M^(m+m)).trans (Nat.le_mul_of_pos_right _ positive)
  have boxes : directory.beforeRows*directory.rows*B ≤ data.records := by
    rw [count]; change _ ≤ directory.beforeRows*directory.rows*directory.beforeH
    rw [shape,← Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ (pow_pos Shared50ModularControl.prime_prime.pos _)
  obtain ⟨_,_,base,_,trailing,_⟩ := inputs.headers
  have shared (i : Fin 66) : raw.R (inner i) = S.R ((i.castAdd (K+1)).castAdd 5) := by
    change S.R ((placement (i.castAdd K)).castAdd 5) = _
    rw [directoryOrdinaryBank_caller]
  obtain ⟨counterUser,A,k,same,paid,build,view,size,keepLeft,regs⟩ := ownerCount_exec
    (fun f => embProg bank id (body f)) (d+1) data.H J M W hm hw u S
    (show M^(d+1)*W = N by rw [← dimension])
    ((shared 2).symm.trans base) ((shared 53).symm.trans trailing)
    (by intro i hi; rw [← shared]; exact free _ (by change 58 ≤ i.val; omega)) width
  change embStk bank A = start at view
  have rawEq := congrArg (embStk placement) view
  let table := projectorResidual finSumFinEquiv (reduce prime proj) (φ ∘ parent) (φ ∘ inv)
  obtain ⟨selectors,y,D,t,user,price,run,prepared,keepL,keepR,projector,liveBits,badBits⟩ :=
    ordinarySelectors_exec localBody proj v parent prefixes archiveTail table directory dirPositive shape pairRoom
      (embDn placement (embDn bank counterUser)) raw free (by simpa only [← count] using inputs)
      beforeRows rows beforeH parents mask mode queueFree
  have controlsPrice := maskSetup_volume_le m w data.records (directory.beforeRows*directory.rows*B)
    privateTapes.length left (data.records*N) (radix.trans (Nat.le_mul_of_pos_left _ recordsPos))
    (Nat.le_mul_of_pos_right _ (radixPos.trans_le radix)) boxes
  refine ⟨selectors,?_⟩
  have queue := owner.trans (congrArg (· ++ ownerTail) (ownerRow_queue (R := data.records) (N := N) rfl word))
  have scan := classifiedDirectory_exec dimension v proj idem adm parent inv (fun i => Ring.mul_inverse_cancel _ (unit i))
    data hm hw positive room fits capacity body c (fun _ => le_rfl) prefixes archiveTail bad budget ordinaryEffect length
    input localBody (fun _ => rfl) selectors goodRow skipRow selectorBudget ownerTail counterUser A (by rwa [view]) (by
    rw [rawEq]
    refine ⟨y,D,t,user,price.trans ?_,run,?_,keepL,keepR,projector,?_,?_⟩
    · simpa only [selectorBudget,List.length_range,count] using controlsPrice
    · simpa only [count,rs] using prepared
    · simpa only [count,rs] using liveBits
    · simpa only [count,rs] using badBits) ((regs 0 (by decide)).trans queue) ((regs 1 (by decide)).trans accumulator) size ((regs 3 (by decide)).trans saved) ((regs 4 (by decide)).trans tmp) (by rwa [view]) (by
    intro j inside regular y A dir payload
    have clear : bad j = false := by
      cases h : live j with
      | true => exact Bool.eq_false_iff.mpr (fun hb => regular ⟨h,hb⟩)
      | false =>
        change fallbackBit _ _ _ = false
        rw [fallbackBit_eq (by omega : 0 < w+1),show LabelStock.live (a+1) (w+1) 1 j = false from h,Bool.false_and]
    have queue : schedule (j::pending (j+1)) = schedule (pending (j+1)) := by
      have hb : actualBad j = false := clear
      simp [schedule,hb]
    obtain ⟨z,D,t,out,user,price,run,next,word,mask,mode,action⟩ := ordinaryOrPadding_exec cap overhead childBudget v proj
      parent prefixes archiveTail schedule hm pool unit space localBody y A j (pending (j+1)) dir queue
      (fun _ => clear) (input j) payload (fun hj => installed j hj clear)
    exact ⟨z,D,t,out,user,price,run,next,action,word,mask,mode⟩)
  obtain ⟨prepare,z,F,t,n,rows,s,midUser,mid,user,bounded,controls,prepared,projector,time,rowTime,run,rowsOk,leftOk,rightOk,rest⟩ := scan
  obtain ⟨output,action,packed⟩ := ownerRows_pack (R := data.records) (N := N) rfl rowsOk
  have finalLeft := leftOk.trans (congrFun keepLeft _)
  have finalRight := rightOk.trans (congrArg (· ++ ownerTail) packed)
  refine ⟨prepare,z,F,t,n,output,k,s,midUser,mid,paid,user.trans same,bounded,
    Exec.seq build controls,prepared,projector.trans (congrArg (fun V : Stacks (66+K) prime => V.R (inner 48)) rawEq),time,rowTime,
    Exec.seq build run,?_,ownerWord_reads word output ownerTail owner reads finalLeft finalRight,finalLeft,finalRight,rest⟩
  intro j
  have row := action j
  change (if live j && bad j then _ else ordinaryEffect j _) at row
  dsimp only [effect]
  cases h : live j with
  | false =>
    simp only [h,Bool.false_and,Bool.false_eq_true,ite_false] at row ⊢
    change (if live j then _ else _) at row
    simpa only [h,Bool.false_eq_true,ite_false] using row
  | true =>
    simp only [h,ite_true,Bool.true_and] at row ⊢
    cases b : bad j with
    | true => simpa only [b,ite_true] using row
    | false =>
      simp only [b,Bool.false_eq_true,ite_false] at row
      change (if live j then _ else _) at row
      letI : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
      apply ordinaryProjectedRead dimension
      simpa only [h,ite_true] using row

/-- Every stopped-child sign program for the 128 fields fits the scanner's state bank. -/
theorem remainderLeafCapacity [M8.Machine.Net] : Record.leafCapacity 128 ≤ columnCapacity := by
  apply max_le le_rfl
  apply Finset.sup_le
  intro i _
  have bound : ∀ i : Fin 128, (fieldSignProgram i true).1 ≤ 11192 := by decide +kernel
  exact (bound i).trans remainderStates_fit

/-- Install a single ordinary body per scheduled PR589 interval. Its private tape
count and cost constants are chosen before the precision or label. -/
theorem remainderDirectoryBody_exists [M8.Machine.Net] {common work : ℕ} {U : Type}
    (e : ℕ × ℕ) (member : e ∈ BitHosting.remainderIntervals) (space : 58 ≤ common+24+31+work) :
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if e.1 ≤ i.val ∧ i.val < e.2 then 1 else 0
    proj.rank = e.2-e.1 ∧ ∃ T, OrdinaryDirectoryBody (d := 63) (Q := columnCapacity) U (le_max_left ..) proj
      (ordinaryCaller (K := common+24+31+(work+T)) (by omega)) := by
  intro proj
  obtain ⟨rank,run⟩ := remainderOrdinary_exec (U := U) e member (le_max_left ..) remainderLeafCapacity (ordinaryCaller space)
  exact ⟨rank,ordinaryDirectoryBody_exists _ proj space run⟩

/-- The scheduled PR589 interval has one classified scanner body at all precisions. -/
theorem scheduledOrdinaryScan_exec [M8.Machine.Net] {common work : ℕ} {U : Type}
    (interval : ℕ × ℕ) (member : interval ∈ BitHosting.remainderIntervals)
    (space : 58 ≤ common+24+31+work) (pool : (RingFormula.conjugationDepth 64+1)*13 ≤ work)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ (common+24+31+work)+1)
    (fits : (36+2*64+1+(RingFormula.conjugationDepth 64+1)*13)+3 ≤ (common+24+31+work)+1) :
    let proj : Matrix (Fin 64) (Fin 64) ℚ := diagonal fun i => if interval.1 ≤ i.val ∧ i.val < interval.2 then 1 else 0
    ∃ T, ∃ localBody : Unit → Pr Unit (66+(common+24+31+(work+T))) columnCapacity prime U,
    ∃ C : ℝ, ∃ overhead : ℕ, ∀ w W, 0 < W →
      let M := prime^(w+1)
      ∃ budget : ℕ, (budget : ℝ) ≤ C*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau*(M^128*W : ℕ) ∧
      ∀ (v : Descriptor) (parent : Fin 64 → ZMod M), (∀ i, IsUnit (parent i)) →
      ∀ data : ScanData 64 127 w W, data.H = M.size →
      ∀ prefixes archiveTail ownerTail,
        ClassifiedOrdinaryScan (a := 63) (d := 127) (J := W.size) v proj (by decide) parent data
          (common := common) (work := work+T) (by omega) (fits.trans (by omega)) remainderAnchorFits (pool.trans (by omega))
          (by omega) (le_max_left ..) overhead budget prefixes archiveTail ownerTail localBody := by
  intro proj
  obtain ⟨_,T,localBody,C,overhead,installed⟩ := remainderDirectoryBody_exists (U := U) interval member space
  refine ⟨T,localBody,C,overhead,?_⟩
  intro w W positive M
  obtain ⟨budget,bill,execute⟩ := installed w W
  refine ⟨budget,bill positive,?_⟩
  intro v parent unit data binary prefixes archiveTail ownerTail
  have adm : Admissible prime proj := by
    intro i j
    simp only [proj,diagonal_apply]
    split_ifs <;> simp
  apply classifiedOrdinaryDirectory_exec v proj (by decide) (intervalDiagonal_idem 64 interval.1 interval.2) adm
    parent unit data (binary ▸ Nat.size_le.mp (le_refl _)) (Nat.size_le.mp (le_refl _)) positive
  intro j live clear g minor
  rw [binary]
  exact execute j live clear parent unit positive minor

end IntegerMultBounds.MathlibTM2.M6.BitNode
