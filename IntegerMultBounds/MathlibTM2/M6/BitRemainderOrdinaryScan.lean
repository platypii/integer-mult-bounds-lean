module

public import IntegerMultBounds.MathlibTM2.M6.BitRemainderScan
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
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4))) (selectorBudget : ℕ)
    (localBody : Unit → Pr Unit (66+(common+24+31+work)) columnCapacity prime U) : Prop :=
    let m := a+1
    let K := common+24+31+work
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let N := M^(m+m)*W
    let inv := fun i => Ring.inverse (parent i)
    let bad := fun j => fallbackBit proj.rank_le_height (reduce M proj) (physicalLabel m (w+1) j)
    let length : N = M^m*(M^m*W) := by simp [N,pow_add,Nat.mul_assoc]
    ∀ (input : ℕ → Fin N → ZMod 2)
      (selectors : Pr Unit (66+K) columnCapacity prime U)
      (u : HS ((66+(K+1))+5) columnCapacity prime U) (S : Stacks ((66+(K+1))+5) prime),
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
    let bits := fun word : Fin N → ZMod 2 => payloadWord (SparseRoleCircuit.encode ∘ word)
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
    let effect := fun j (next : Fin N → ZMod 2) => if live j && bad j then
      ∀ x k, next ((FlatCoordinateLayout.index ((projectorResidual e (reduce (prime^(w+1)) proj) parent inv
        (physicalLabel m (w+1) j)).mulVec x) k).cast (directoryPayloadLength e length)) =
        input j ((FlatCoordinateLayout.index x k).cast (directoryPayloadLength e length))
      else ordinaryEffect j next
    start.R (directoryMatrixTape room) = [] →
    (∃ y D t, y.user = u.user ∧ t ≤ selectorBudget ∧
      Exec localBody selectors (mk (embDn placement (embDn bank u)) (embStk placement start)) t (mk y D) ∧
      ready D rs ∧ D.L (inner 24) = (embStk placement start).L (inner 24) ∧
      D.R (inner 24) = (embStk placement start).R (inner 24) ∧
      D.R (inner 48) = (embStk placement start).R (inner 48) ∧
      D.R (inner 57) = rs.map (fun j => bitSymbol (live j)) ∧ D.R (inner 56) = rs.map (fun j => bitSymbol (bad j))) →
    S.R (reg 0) = rs.flatMap (bits ∘ input) ++ ownerTail → S.R (reg 1) = [] → (S.R (reg 2)).length = N →
    S.R (reg 3) = [] → S.R (reg 4) = [] → (∀ j, readAt blank (start.L (caller 24)) (start.R (caller 24)) j = blank) →
    let program := packedOwner (caller 24) (caller 57) (ownerDispatch (caller 57) (caller 56) good
      (directoryExceptionalProgram m d room capacity) padding)
    let work := (List.finRange (66+(K+1))).filter fun i => decide (58 ≤ i.val ∧ i ≠ directoryMatrixTape room)
    let controls := embProg bank id (embProg placement id selectors)
    ∃ prepare z F t n rows s midUser mid, z.user = u.user ∧ s ≤ selectorBudget ∧
      Exec (fun f => embProg bank id (body f)) controls (mk u S) s (mk midUser mid) ∧
      ready (embStk placement (embStk bank mid)) rs ∧
      (embStk bank mid).R (caller 48) = (embStk placement start).R (inner 48) ∧
      let initTime := directoryQueueInitTime m d w data.H data.records (embStk bank mid)
      let queueTime := directoryMatrixQueueTime m d w data.H data.records ((embStk bank mid).R (caller 47)).length

      (∀ p, mnProgPush prepare ≤ p → (∀ f, mnProgPush (body f) ≤ p) →
        t ≤ initTime + queueTime + (4*work.length+1+work.length*(6*(p*initTime)))) ∧
      n ≤ (rs.map (fun j => 6*N+6+cost j+(4*N+4))).sum + 2*rs.length+2 + (2*(rs.length*N)+2) ∧
      Exec (fun f => embProg bank id (body f)) (controls.seq ((embProg bank id prepare).seq program)) (mk u S) (s+(t+n)) (mk z F) ∧
      List.Forall₂ (fun j out => ∃ word, effect j word ∧ out = bits word) rs rows ∧
      F.L (reg 0) = S.L (reg 0) ∧ F.R (reg 0) = rows.flatten ++ ownerTail ∧ F.R (reg 1) = [] ∧ ready (embStk placement (embStk bank F)) [] ∧
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
    (prefixes : ℕ → List (Fin (prime+4))) (archiveTail ownerTail : List (Fin (prime+4))) (selectorBudget : ℕ) :
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
      prefixes archiveTail ownerTail selectorBudget localBody := by
  intro m K M N inv bad length localBody installed
  unfold ClassifiedOrdinaryScan
  intro _ _ _ _ _ actualBad _ input selectors u S body c core ports skipRow step scratch goodRow push budget ordinaryEffect
  intro e physical φ code schedule ready placement caller live rs pending bits bank reg start inner advance good padding ordinaryTime cost effect
    matrix generated owner accumulator width saved tmp empty
  apply classifiedDirectory_exec dimension v proj idem adm parent inv (fun i => Ring.mul_inverse_cancel _ (unit i))
    data hm hw positive room fits capacity body c (fun _ => le_rfl) prefixes archiveTail bad budget ordinaryEffect length
    input localBody (fun _ => rfl) selectors goodRow skipRow selectorBudget ownerTail u S matrix generated owner accumulator width saved tmp empty
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
  exact ⟨z,D,t,out,user,price,run,next,action,word,mask,mode⟩

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
      ∀ prefixes archiveTail ownerTail selectorBudget,
        ClassifiedOrdinaryScan (a := 63) (d := 127) (J := W.size) v proj (by decide) parent data
          (common := common) (work := work+T) (by omega) (fits.trans (by omega)) remainderAnchorFits (pool.trans (by omega))
          (by omega) (le_max_left ..) overhead budget prefixes archiveTail ownerTail selectorBudget localBody := by
  intro proj
  obtain ⟨_,T,localBody,C,overhead,installed⟩ := remainderDirectoryBody_exists (U := U) interval member space
  refine ⟨T,localBody,C,overhead,?_⟩
  intro w W positive M
  obtain ⟨budget,bill,execute⟩ := installed w W
  refine ⟨budget,bill positive,?_⟩
  intro v parent unit data binary prefixes archiveTail ownerTail selectorBudget
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
