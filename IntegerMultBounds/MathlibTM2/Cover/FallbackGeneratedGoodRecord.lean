module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRoundTrip
public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugationQueue
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInit

/-! Read a live directory label, compute the conjugate, and run the good-record round trip. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout Matrix Finset IntegerMultBounds.Swap.LowerTriangular
  IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

/-- Read the modulus and the unit from the caller. The other reciprocal
registers borrow the elimination bank before elimination starts. -/
def goodRecordPivotPorts : Fin 16 ↪ Fin 82 :=
  ⟨![58,59,60,61,2,63,64,65,66,67,68,69,70,74,72,44],by decide⟩

def goodRecordCounterPorts : Fin 2 ↪ Fin 82 := ⟨![45,73],by decide⟩

/-- Seven caller tapes hold the directory inputs. The remaining eleven
registers borrow blank elimination tapes until the matrix is produced. -/
def goodRecordDirectoryPorts (headers : Fin 7 ↪ Fin 58) : Fin 18 ↪ Fin 82 :=
  let order : Fin 18 ↪ Fin (7+11) := ⟨![7,0,1,8,9,10,11,12,2,3,13,14,4,15,16,17,5,6],by decide⟩
  let scratch : Fin 11 ↪ Fin 24 := ⟨![2,3,4,5,6,7,17,8,9,10,11],by decide⟩
  ((order.trans finSumFinEquiv.symm.toEmbedding).trans (headers.sumMap scratch)).trans finSumFinEquiv.toEmbedding

open RingFormula LabelTraversal in
theorem generatedGoodRecordRoundTrip_exec [M8.Machine.Net] {T m work Q fields H J W : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (label : ℕ) (live : LabelStock.live m (w+1) 1 label = true)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (roles : Tapes T prime)
    (f : ℤ → Fin (prime+4)) (p : ℤ) (node scalar : Tapes 1 prime)
    (arity : ℕ) (st : Tapes 2 prime) (freeNode : Family.NodeFree node)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (length : volume prime v = (prime^(w+1))^fields*((prime^(w+1))^fields*W))
    (capacity : 217 ≤ Q) (source : ℤ → Fin 4) (head : ℤ)
    (fits : LeafCore.small ≤ work) (cap : (LeafCore.core io).states ≤ Q) :
    let d := proj.rank
    let common := CommonBank.count T
    let host := common+24
    let M := prime^(w+1)
    let N := volume prime v
    let entry : Graph.Block common prime := Blocks.seqB LeafRoutines.offsets (Blocks.seqB Blocks.push LeafRoutines.view)
    let leave : Graph.Block common prime := Blocks.seqB Blocks.restore LeafRoutines.advance
    let record := (Fin.natAddEmb common (m := 24)).trans ((Fin.castAddEmb 31).trans (Fin.castAddEmb work))
    let bank := (Fin.castLEEmb (by decide : 23 ≤ 24)).trans record
    let g := physicalLabel m (w+1) label
    let G := g*reduce M proj*g⁻¹
    let rep := fun count roles' (D : Stacks ((host+31)+work) prime) =>
      RepT (CommonBank.bank roles' (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d count) st)
        (fun k => D.L (((k.castAdd 24).castAdd 31).castAdd work))
        (fun k => D.R (((k.castAdd 24).castAdd 31).castAdd work))
    let clean := fun (D : Stacks ((host+31)+work) prime) => ∀ (k : Fin work) x,
      readAt blank (D.L (k.natAdd (host+31))) (D.R (k.natAdd (host+31))) x = blank
    let logical := {v with width := d}
    let addr := fun a row pre mid post (x : IntegerMultBounds.Swap.Shear.State (Fin d) (ZMod M)) =>
      index M logical a row pre (FlatCoordinateLayout.rank x.1).val mid (FlatCoordinateLayout.rank x.2).val post
    let inner := Fin.natAddEmb 66 (m := (host+31)+work)
    let caller := Fin.castAddEmb (n := 66) ((host+31)+work)
    let K := 66+((host+31)+work)
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F K Q prime U)
      (u : HS _ Q prime U) (whole : Stacks K prime),
      ∀ (headers : Fin 7 ↪ Fin 58) (poolFits : (conjugationDepth m+1)*13 ≤ work) (ancestor tail : List (Fin (prime+4))),
      let joined := recordLoaderBank record
      let dirSlots := goodRecordDirectoryPorts headers
      let dir := dirSlots.trans joined
      let pool := ((Fin.castLEEmb poolFits).trans (Fin.natAddEmb (host+31))).trans inner
      let pivot := goodRecordPivotPorts.trans joined
      let counters := goodRecordCounterPorts.trans joined
      headers 2 = 2 → headers 6 = 44 →
      let inputs := sourcePorts (m := m) (QueueLayout.formulaInputs.trans dir) id
      let ports := QueueLayout.normalizationPorts.trans pivot
      let a := QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans dir)
      let digits := QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans dir)
      let prefixWidth := dir 12
      let zeros := dir 9
      let packedLabel := dir 10
      let clock := counters 0
      let count := counters 1
      let formula := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
      let formulaCost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (formula ij.1 ij.2)
      let detFormula := determinant (matrixInput (m := m) false)
      let C := 48*H*H+152*H+66
      let generation := ((m*(m*(12*ancestor.length+8*((w+1)*(m*m))+(w+1)*(7*H+prime+31)+10*H+42)+1)+1) + (time H (readTime H) detFormula + (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) +
       ((m*(m*(formulaCost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) + (2*(m*m*H)+2))
      let generate : Pr F K Q prime U := (.seq (directoryMatrix m a digits prefixWidth zeros packedLabel) (.seq (.seq (.seq (compile (readLeaf (leafBank inputs)) (registerBank pool) detFormula 0 (pivot 14)) (reusablePivotInverse prime pivot clock count))
        (.seq (packedConjugate pool inputs ports false true) (.seq (bclear (pivot 0)) (bclear (pivot 14))))) (bclear packedLabel)))
      let field := fun i => caller ((headers i).castAdd 8)
      whole.R (field 1) = ancestor ++ (LabelDirectory.digits m (w+1) label).map RadixDigits.digitSymbol ++ tail →
      (whole.R (field 4)).length = ancestor.length → (whole.R (field 0)).length = w+1 →
      whole.R (field 3) = binSyms H 0 → (∀ j, whole.R (pool j) = []) →
      (∃ suffix, whole.R (field 5) = matrixWords prime H (reduce M proj) ++ suffix) →
      let slot := (((LeafCore.roleSlot io).castAdd 24).castAdd 31).castAdd work
      let r := recordRoundTripPorts slot
      let S := embStk inner whole
      whole.R (caller 2) = binSyms H M → whole.R (caller 28) = binSyms 1 1 →
      whole.R (caller 53) = binSyms J W →
      (∀ i : Fin 66, 58 ≤ i.val → whole.L (caller i) = [] ∧ whole.R (caller i) = []) →
      (∀ z, readAt blank (whole.L (r 0)) (whole.R (r 0)) (z-head) =
        RadixToBinary.binaryEncoding.encode (putWord source head ((List.ofFn word).map SparseRoleCircuit.encode) z)) →
      (∀ z, readAt blank (whole.L (r 1)) (whole.R (r 1)) z = blank) →
      rep d roles S → clean S →
      (∀ k : Fin 31, S.L ((k.natAdd host).castAdd work) = [] ∧ S.R ((k.natAdd host).castAdd work) = []) →
      fallbackBit rankFits (reduce M proj) g = false →
      whole.R (caller 44) = binSyms H (1 : ZMod M).val → (whole.R (caller 45)).length = w →
      whole.R (caller 55) = (List.ofFn fun i => binSyms H (parent i).val).flatten →
      (∀ i : Fin 24, i ≠ 16 → S.R (record i) = []) →
      let call := fun i : Fin d => packedCoordinateProgram (F := Empty) (U := U) io i.val i.val ef xf fits eqs xqs cap
      let cost := packedCoordinatesTime d N w (LeafCore.core io).tapes
        (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
      let budget := (d*(4*w+4+columnTime m prime w M.size)+1+(d*(8*(m*m*M.size)+14*M.size+22)+1))+cost
      let coordinate := (goodWeights prime d rankFits bank).seq (Prog.seqList ((List.finRange d).reverse.map call))
      let effect := fun ys : List (ZMod 2) =>
        ∃ minor : ∀ k (hk : k < d), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk rankFits) G).det,
        let stage := GoodForm.stageAt G d rankFits minor d le_rfl
        let pivot := fun i : Fin d => stage.M (i.castLE rankFits) (i.castLE rankFits)
        let weight := fun i : Fin d => parent (i.castLE rankFits)*pivot i
        let inv := fun i : Fin d => parentInv (i.castLE rankFits)*Ring.inverse (pivot i)
        ∃ next : Fin N → ZMod 2, ys = List.ofFn next ∧
          ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
            ext next (addr a row pre mid post (Weighted.child d weight inv x)) = ext word (addr a row pre mid post x)
      let reverse := (Equiv.swap (0 : Fin 8) 1).toEmbedding.trans r
      let transfer := fun ports : Fin 8 ↪ Fin K => (stateLiftNormalize capacity (by decide)).seq
        (stateLiftPr capacity (by decide) Empty.elim (returnFromOrigin (P := Empty) ports))
      let marks := ([2,3,4,5,6,7] : List (Fin 8)).map r
      let packed := (List.ofFn fun i => binSyms (A := prime) M.size (parent i).val).flatten
      let loading := ((6*(whole.R (caller 55)).length+6)+((10*H+12)+(m*(10*M.size+8*(H-M.size)+12)+1+
        (2*packed.length+2))))+((10*M.size+10)+(6*(whole.R (caller 45)).length+6))
      let conversion := (m*m)*(10*M.size+8*(H-M.size)+12)+1+(2*(matrixWords prime M.size G).length+2)
      ∃ z D t ys, z.user = u.user ∧ t ≤ ((conjugationDepth m+1)*(6*H+6)+1 + (generation+((conjugationDepth m+1)*(2*H+2)+1))) + ((dimensionTime H 1 fields+(4*(fields*H+1)+6)+(10*J+12)+(6*(M^fields).size+6)) +
        (loading+(conversion+(budget+2*((218*N+1)*13+6)+3)))) ∧
        Exec body (((initFrames pool (pivot 4) (conjugationDepth m+1)).seq (generate.seq (clearFrames pool (conjugationDepth m+1)))).seq ((recordCounterSetup caller fields).seq ((recordInputProgram record m).seq ((recordMatrixProgram record m).seq ((.act (pushMarkers marks) : Pr F K Q prime U).seq
          ((transfer r).seq ((embProg inner Empty.elim coordinate).seq (transfer reverse)))))))) (mk u whole) t (mk z D) ∧
        effect ys ∧ (∀ k, readAt blank (D.L (r 0)) (D.R (r 0)) (k-head) =
          RadixToBinary.binaryEncoding.encode (putWord source head (ys.map SparseRoleCircuit.encode) k)) ∧
        ∀ j : Fin 58, j ≠ 24 → let port := caller (j.castAdd 8)
          D.L port = whole.L port ∧ D.R port = whole.R port := by
  intro d common host M N entry leave record bank g G rep clean logical addr inner caller K ef xf eqs xqs word
    body u whole headers poolFits ancestor tail joined dirSlots dir pool pivot counters widthSlot unitSlot inputs ports a digits prefixWidth zeros
    packedLabel clock count formula formulaCost detFormula C generation generate field dirInput prefixInput atomInput zeroInput poolBlank projectorInput slot r S base unit trailing spare input blank initial free empty good
    one ticks archive scratch call cost budget coordinate effect reverse transfer marks packed loading conversion

  let mat := fun b : Bool => if b then reduce M proj else g
  let out := inner (record 16)
  have depthFits (i j : Fin m) : (formula i j).depth ≤ conjugationDepth m :=
    le_trans (Finset.le_sup (f := fun ij : Fin m × Fin m => (formula ij.1 ij.2).depth) (Finset.mem_univ (i,j)))
      (Nat.le_max_right _ _)
  have poolOff (i : Fin 82) (j) : joined i ≠ pool j := by
    refine Fin.addCases (m := 58) (n := 24) (motive := fun i => joined i ≠ pool j) ?_ ?_ i
    · intro k eq
      rw [show joined (k.castAdd 24) = caller (k.castAdd 8) from recordLoaderBank_caller record k] at eq
      have h := congrArg Fin.val eq
      change k.val = 66+(host+31+j.val) at h
      omega
    · intro k eq
      rw [show joined (k.natAdd 58) = inner (record k) from recordLoaderBank_private record k] at eq
      have h := congrArg Fin.val (inner.injective eq)
      change common+k.val = host+31+j.val at h
      dsimp only [host] at h
      omega
  have bp (i j) : dir i ≠ pool j := poolOff _ _
  have rp (i j) : pivot i ≠ pool j := poolOff _ _
  have cp (i j) : counters i ≠ pool j := poolOff _ _
  have br (i j) (h : i = 10 ∨ j ∈ ([0,1,12,14] : List (Fin 16))) : dir i ≠ pivot j := by
    apply joined.injective.ne
    by_cases hi : i = 10
    · subst i; exact (by decide : ∀ j, (75 : Fin 82) ≠ goodRecordPivotPorts j) j
    · have hj := h.resolve_left hi
      let scratchSlots : Fin 11 → Fin 24 := ![2,3,4,5,6,7,17,8,9,10,11]
      have allSlots (l : Fin (7+11)) :
          finSumFinEquiv (Sum.map headers scratchSlots (finSumFinEquiv.symm l)) ≠ goodRecordPivotPorts j := by
        induction l using Fin.addCases with
        | left k =>
          rw [finSumFinEquiv_symm_apply_castAdd]
          exact (by decide : ∀ k : Fin 58, ∀ j ∈ ([0,1,12,14] : List (Fin 16)), k.castAdd 24 ≠ goodRecordPivotPorts j) (headers k) j hj
        | right k =>
          rw [finSumFinEquiv_symm_apply_natAdd]
          exact (by decide : ∀ k : Fin 11, ∀ j ∈ ([0,1,12,14] : List (Fin 16)),
          ((![2,3,4,5,6,7,17,8,9,10,11] k : Fin 24).natAdd 58) ≠ goodRecordPivotPorts j) k j hj
      exact allSlots _
  have clockOff : packedLabel ≠ clock := joined.injective.ne (by decide : (75 : Fin 82) ≠ 45)
  have countOff : packedLabel ≠ count := joined.injective.ne (by decide : (75 : Fin 82) ≠ 73)
  have rc (i j) : pivot i ≠ counters j :=
    joined.injective.ne ((by decide : ∀ i j, goodRecordPivotPorts i ≠ goodRecordCounterPorts j) i j)
  have output : pivot 13 = inner (record 16) := recordLoaderBank_private record 16
  have copyPorts : [clock,count,pivot 2,pivot 3].Nodup := by
    simp [clock,count,counters.injective.eq_iff,pivot.injective.eq_iff,Ne.symm (rc _ _)]
  have atOutput : ports 3 = out := output
  have modulusWord : whole.R (pivot 4) = binSyms H M := by
    rw [show pivot 4 = caller 2 from recordLoaderBank_caller record 2]; exact base
  have unitWord : whole.R (pivot 15) = binSyms H (1 : ZMod M).val := by
    rw [show pivot 15 = caller 44 from recordLoaderBank_caller record 44]; exact one
  have clockWidth : (whole.R clock).length = w := by
    rw [show clock = caller 45 from recordLoaderBank_caller record 45]; exact ticks
  have regEmpty (i : Fin 24) (hi : i ≠ 16) : whole.R (joined (i.natAdd 58)) = [] := by
    rw [recordLoaderBank_private]; exact scratch i hi
  have dirEmpty (i : Fin 18) (hi : i ∈ [0,3,4,5,6,7,10,11,14,15]) : whole.R (dir i) = [] := by
    revert hi
    fin_cases i <;> simp <;> exact regEmpty _ (by decide)
  have header (i : Fin 7) : joined ((headers i).castAdd 24) = field i := recordLoaderBank_caller record (headers i)
  have directoryWord := (congrArg whole.R (header 1)).trans dirInput
  have prefixLen := (congrArg (fun i => (whole.R i).length) (header 4)).trans prefixInput
  have fieldWidth := (congrArg (fun i => (whole.R i).length) (header 0)).trans atomInput
  have zeroWord := (congrArg whole.R (header 3)).trans zeroInput
  have projector : ∃ suffix, whole.R (dir 16) = matrixWords prime H (reduce M proj) ++ suffix := by
    change ∃ suffix, whole.R (joined ((headers 5).castAdd 24)) = _
    rwa [header]
  have packedEmpty := dirEmpty 10 (by decide)
  have widthPort : dir 8 = caller 2 := by
    change joined ((headers 2).castAdd 24) = _
    rw [widthSlot]; exact recordLoaderBank_caller record 2
  have unitPort : dir 17 = caller 44 := by
    change joined ((headers 6).castAdd 24) = _
    rw [unitSlot]; exact recordLoaderBank_caller record 44
  have inputOne := (congrArg whole.R unitPort).trans one
  have digitWidth : (whole.R (digits 4)).length = H := by
    change (whole.R (dir 8)).length = H
    rw [widthPort,base,length_binSyms]
  have freeRead (i : Fin 7) (hi : i = 0 ∨ 3 ≤ i) : whole.R (a i) = [] :=
    dirEmpty _ ((by decide : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i → QueueLayout.directoryWork (QueueLayout.readPorts i) ∈
      ([0,3,4,5,6,7,10,11,14,15] : List (Fin 18))) i hi)
  have freeDigit (i : Fin 6) (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5) : whole.R (digits i) = [] :=
    dirEmpty _ ((by decide : ∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 → QueueLayout.directoryWork (QueueLayout.digitPorts i) ∈
      ([0,3,4,5,6,7,10,11,14,15] : List (Fin 18))) i hi)
  have pivotEmpty (i : Fin 16) (hi : i ≠ 4 ∧ i < 13 ∨ i = 14) : whole.R (pivot i) = [] := by
    obtain ⟨j,ne,eq⟩ := (by decide : ∀ i : Fin 16, i ≠ 4 ∧ i < 13 ∨ i = 14 →
      ∃ j : Fin 24, j ≠ 16 ∧ goodRecordPivotPorts i = j.natAdd 58) i hi
    change whole.R (joined (goodRecordPivotPorts i)) = []
    rw [eq]; exact regEmpty j ne
  let B : Stacks K prime := {whole with R := Function.update whole.R out (matrixWords prime H G ++ whole.R out)}
  obtain ⟨y,n,hy,hn,runWriter⟩ := withFrames_exec body pool (pivot 4) out (rp 4) (by change ∀ j, inner (record 16) ≠ pool j; rw [← output]; exact rp 13)
    generate (matrixWords prime H G) generation u whole poolBlank (by
    intro v' E stable filled frames
    let R := Function.update E.R packedLabel (matrixWords prime H g)
    have updated (i) (hi : ∀ j, i ≠ pool j) (ne : packedLabel ≠ i) : R i = whole.R i :=
      (Function.update_of_ne ne.symm _ _).trans (stable i hi)
    have pivotKept (i) := updated (pivot i) (rp i) (br 10 i (Or.inl rfl))
    have keep (i : Fin 18) (hi : i ≠ 10) : R (dir i) = whole.R (dir i) :=
      (Function.update_of_ne (dir.injective.ne hi) _ _).trans (stable _ (bp i))
    let sources := QueueLayout.formulaInputs.trans dir
    have matrices (b : Bool) : ∃ suffix, R (sources (if id b then 7 else 2)) = matrixWords prime H (mat b) ++ suffix := by
      cases b
      · exact ⟨[],by simp [R,sources,QueueLayout.formulaInputs,packedLabel,mat]⟩
      · change ∃ suffix, R (dir 16) = matrixWords prime H (reduce M proj) ++ suffix
        rwa [keep 16 (by decide)]
    have leaves := sourcePorts_ready sources id mat H R matrices
      ((congrArg List.length (keep 8 (by decide))).trans digitWidth)
      ((keep 9 (by decide)).trans zeroWord) ((keep 17 (by decide)).trans inputOne)
      (fun i hi => by
        have ok := (by decide : ∀ i ∈ ([0,4,5,6] : List (Fin 10)), ∃ j : Fin 7,
          (j = 0 ∨ 3 ≤ j) ∧ QueueLayout.formulaInputs i = QueueLayout.directoryWork (QueueLayout.readPorts j) ∧
          QueueLayout.formulaInputs i ≠ 10) i hi
        obtain ⟨j,hj,eq,ne⟩ := ok
        exact (keep _ ne).trans ((congrArg whole.R (congrArg dir eq)).trans (freeRead j hj)))
    have scratchPort : ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 →
        QueueLayout.normalizationPorts k ≠ 4 ∧ QueueLayout.normalizationPorts k < 13 := by decide
    have gen := physicalConjugation_writes body w label mat false true rfl live pivot clock count copyPorts
      (fun i => rc i 1) (rc 14 0).symm H hm pool inputs (fun _ _ j => bp _ j) ports
      (fun k => (rp 14 k).symm) (fun _ _ => br _ 14 (Or.inr (by decide))) (fun k => (rp 0 k).symm) (fun _ _ => br _ 0 (Or.inr (by decide)))
      (fun j => pivot.injective.ne ((by decide : ∀ j, QueueLayout.normalizationPorts j ≠ 14) j)) rfl
      (fun k _ _ => (rp _ k).symm) packedLabel (br 10 13 (Or.inl rfl)) a digits rfl
      (fun i j => ((by decide : ∀ i j, QueueLayout.readPorts i ≠ QueueLayout.digitPorts j ∨ i = 3 ∧ j = 0) i j).imp
        (fun h => (QueueLayout.directoryWork.trans dir).injective.ne h) id)
      prefixWidth zeros (by change [dir 12,dir 0,dir 6].Nodup; simp)
      (by change [dir 12,dir 9,dir 10].Nodup; simp) (dir.injective.ne (by decide : (12 : Fin 18) ≠ 7))
      (fun i => dir.injective.ne ((by decide : ∀ i, QueueLayout.directoryWork (QueueLayout.readPorts i) ≠ 10) i))
      (fun i => dir.injective.ne ((by decide : ∀ i, QueueLayout.directoryWork (QueueLayout.digitPorts i) ≠ 10) i))
      (fun i => dir.injective.ne ((by decide : ∀ i, 9 ≠ QueueLayout.directoryWork (QueueLayout.digitPorts i)) i)) ancestor tail (fun _ _ j hj => br _ _ (Or.inr ((by decide : ∀ j : Fin 14, j = 1 ∨ j = 13 →
        QueueLayout.normalizationPorts j ∈ ([0,1,12,14] : List (Fin 16))) j hj)))
      depthFits (Nat.le_max_left _ _) v' E
      ⟨by
          exact ⟨(stable _ (bp _)).trans directoryWord, (congrArg List.length (stable _ (bp _))).trans prefixLen,
            (congrArg List.length (stable _ (bp _))).trans fieldWidth,fun i hi => (stable _ (bp _)).trans (freeRead i hi),
            (congrArg List.length (stable _ (bp _))).trans digitWidth, fun i hi => (stable _ (bp _)).trans (freeDigit i hi),
            (stable _ (bp _)).trans zeroWord⟩,
        (stable _ (bp _)).trans packedEmpty,(congrArg List.length (updated clock (cp 0) clockOff)).trans clockWidth,
        (updated count (cp 1) countOff).trans (regEmpty 15 (by decide)),(pivotKept 14).trans (pivotEmpty 14 (by decide)),(pivotKept 15).trans unitWord,
        (pivotKept 4).trans modulusWord,fun i h l => (pivotKept i).trans (pivotEmpty i (Or.inl ⟨h,l⟩)),
        fun k hk => (Function.update_of_ne (bp 10 _).symm _ _).trans ((filled k hk).trans modulusWord),
        fun k hk i hi => (Function.update_of_ne (bp 10 _).symm _ _).trans (frames k hk i hi),leaves,
        (pivotKept 4).trans modulusWord,(pivotKept 12).trans (pivotEmpty 12 (by decide)),
        fun k hk => (pivotKept _).trans (pivotEmpty _ (Or.inl (scratchPort k hk)))⟩
    simpa only [atOutput,mat,G,Bool.false_eq_true,ite_false,ite_true] using gen)
  rw [modulusWord,length_binSyms] at hn
  have callerOff (i : Fin 66) : caller i ≠ out := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = 66+(record 16).val at h
    omega
  have preserved (i : Fin 66) : B.R (caller i) = whole.R (caller i) := Function.update_of_ne (callerOff i) _ _
  have privateOff (j) (h : j.val < common ∨ host ≤ j.val) : inner j ≠ out := by
    intro eq
    have hit := congrArg Fin.val (inner.injective eq)
    change j.val = common+16 at hit
    dsimp only [host] at h
    omega
  have privateKept (j) (h : j.val < common ∨ host ≤ j.val) : B.R (inner j) = whole.R (inner j) :=
    Function.update_of_ne (privateOff j h) _ _
  have first : r 0 = caller 24 := recordRoundTripPorts_other slot 0 (by decide)
  have shared : inner slot = r 1 := (recordRoundTripPorts_shared slot).symm
  obtain ⟨z,D,t,ys,hz,ht,run,act,read,frame⟩ := goodRecordRoundTrip_exec
    v positive w proj width idem factor hd label live rankFits parent parentInv reciprocal io roles f p node scalar
    arity st freeNode hm hw hW length capacity source head fits cap ef xf eqs xqs word body y B (whole.R out)
    ((preserved 2).trans base) ((preserved 28).trans unit) ((preserved 53).trans trailing)
    (fun i hi => ⟨(spare i hi).1,(preserved i).trans (spare i hi).2⟩)
    (by intro z; change readAt _ (whole.L (r 0)) (B.R (r 0)) _ = _; rw [first,preserved]; simpa only [first] using input z)
    (by intro z; change readAt _ (whole.L (r 1)) (B.R (r 1)) _ = _; rw [← shared,privateKept _ (Or.inl (LeafCore.roleSlot io).isLt)]; simpa only [← shared] using blank z)
    (by intro k x
        change _ = readAt _ _ (B.R (inner (((k.castAdd 24).castAdd 31).castAdd work))) _
        rw [privateKept _ (Or.inl k.isLt)]
        exact initial k x)
    (by intro k x
        change readAt _ _ (B.R (inner (k.natAdd (host+31)))) _ = _
        rw [privateKept _ (Or.inr (by simp; omega))]
        exact free k x)
    (fun k => ⟨(empty k).1,(privateKept ((k.natAdd host).castAdd work) (Or.inr (by simp))).trans (empty k).2⟩)
    good (by change B.R out = _; simp [B,G,g,M])
    ((preserved 44).trans one) ((congrArg List.length (preserved 45)).trans ticks)
    ((preserved 55).trans archive)
    (by intro i hi
        exact (Function.update_of_ne (inner.injective.ne (record.injective.ne hi)) _ _).trans (scratch i hi))
  refine ⟨z,D,_,ys,hz.trans hy,Nat.add_le_add hn ?_,Exec.seq runWriter run,act,read,?_⟩
  · rw [show B.R ((Fin.castAddEmb (CommonBank.count T+24+31+work)) 55) = whole.R (caller 55) from preserved 55,
      show B.R ((Fin.castAddEmb (CommonBank.count T+24+31+work)) 45) = whole.R (caller 45) from preserved 45] at ht
    exact ht
  · intro j ne
    exact ⟨(frame j ne).1,(frame j ne).2.trans (preserved _)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
