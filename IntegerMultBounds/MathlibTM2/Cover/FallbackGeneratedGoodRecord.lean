module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRoundTrip
public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugationQueue
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaInit
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordCleanup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordHeaders
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordMasks
public import IntegerMultBounds.MathlibTM2.Cover.FallbackRecordCounters

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

/-- Six caller tapes hold the directory inputs. The remaining twelve
registers borrow blank elimination tapes until the matrix is produced. -/
def goodRecordDirectoryPorts (headers : Fin 6 ↪ Fin 58) : Fin 18 ↪ Fin 82 :=
  let order : Fin 18 ↪ Fin (6+12) := ⟨![6,0,1,7,8,9,10,11,2,17,12,13,3,14,15,16,4,5],by decide⟩
  let scratch : Fin 12 ↪ Fin 24 := ⟨![2,3,4,5,6,7,17,8,9,10,11,18],by decide⟩
  ((order.trans finSumFinEquiv.symm.toEmbedding).trans (headers.sumMap scratch)).trans finSumFinEquiv.toEmbedding

/-- Borrow a blank register for the padded zero word and release it after
the matrix writer has consumed the constant. -/
theorem withRecordZero_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (src zero tmp dst : Fin T) (ports : [src,zero,tmp].Nodup) (apart : dst ≠ zero)
    (program : Pr P T Q A U) (word : List (Fin (A+4))) (cost : ℕ)
    (u : HS T Q A U) (S : Stacks T A) (blank : S.R zero = []) (free : S.R tmp = []) :
    let H := (S.R src).length
    let B := {S with R := Function.update S.R zero (binSyms H 0)}
    (∀ v : HS T Q A U, ∃ y n, y.user = v.user ∧ n ≤ cost ∧ Exec body program (mk v B) n
      (mk y {B with R := Function.update B.R dst (word ++ B.R dst)})) →
    ∃ z t, z.user = u.user ∧ t ≤ (4*H+4)+(cost+(2*H+2)) ∧
      Exec body ((Node.umulSym 1 (bitSymbol false) src zero tmp).seq (program.seq (bclear zero)))
        (mk u S) t (mk z {S with R := Function.update S.R dst (word ++ S.R dst)}) := by
  intro H B writer
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,not_or] at ports
  obtain ⟨v,hv,fill⟩ := Node.umulSym_exec body 1 (bitSymbol false) ports.1.1 ports.1.2.1 ports.2.1.1 u S free
  have code : binSyms (A := A) H 0 = List.replicate H (bitSymbol false) := by simp [binSyms,List.ofFn_const]
  rw [Nat.one_mul,blank,List.append_nil,← code] at fill
  obtain ⟨y,n,hy,hn,run⟩ := writer v
  let E := {B with R := Function.update B.R dst (word ++ B.R dst)}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body zero y E
  have len : (E.R zero).length = H := by simp [E,B,apart.symm,length_binSyms]
  rw [len] at clear
  refine ⟨z,_,hz.trans (hy.trans hv),Nat.add_le_add_left (Nat.add_le_add_right hn _) _,Exec.seq fill (Exec.seq run ?_)⟩
  simpa only [E,B,Function.update_of_ne apart,Function.update_comm apart,
    Function.update_idem,← blank,Function.update_eq_self] using clear

/-- The directory reader needs one more digit than the reciprocal clock.
Borrow the clock for the read and restore it before computing the reciprocal. -/
def readWithSuccessorClock {T Q A : ℕ} {P U : Type} (clock : Fin T) (reader : Pr P T Q A U) : Pr P T Q A U :=
  Prog.seq (.act (.push (.rt clock) (fun _ => Node.tick) .done)) (reader.seq (.act (Node.dropTop clock .done)))

open LabelTraversal in
theorem readWithSuccessorClock_writes {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (clock dst : Fin T) (apart : clock ≠ dst) (ok : Node.Regs T A → Prop)
    (reader : Pr P T Q A U) (word : List (Fin (A+4))) (cost : ℕ)
    (read : Writes body ok dst reader word cost) :
    Writes body (fun R => ok (Function.update R clock (Node.tick :: R clock))) dst
      (readWithSuccessorClock clock reader) word (1+(cost+1)) := by
  intro u S ready
  let D := {S with R := Function.update S.R clock (Node.tick :: S.R clock)}
  have push : Exec body (.act (.push (.rt clock) (fun _ => Node.tick) .done)) (mk u S) 1 (mk u D) := by
    simpa [D,Action.run,update_rt] using Exec.act (body := body) (.push (.rt clock) (fun _ => Node.tick) .done) (mk u S)
  obtain ⟨y,n,hy,hn,run⟩ := read u D ready
  let E := {D with R := Function.update D.R dst (word ++ D.R dst)}
  have pop := Exec.act (body := body) (Node.dropTop clock .done) (mk y E)
  refine ⟨y,1+(n+1),hy,by omega,Exec.seq push (Exec.seq run ?_)⟩
  have restore (xs) : Function.update (Function.update S.R dst xs) clock (S.R clock) = Function.update S.R dst xs := by
    funext i; by_cases h : i = clock <;> simp [h,apart]
  simpa [restore,E,D,Node.dropTop,Action.run,update_rt,Function.update_comm apart,apart,apart.symm] using pop

private theorem emptyCommonTape {T : ℕ} (hs : Fin 6 → List Bool) (c : Fin 24 → Option ℕ)
    (k : Fin (CommonBank.count T)) (ha : ∀ i, CommonBank.auxSlot i ≠ k)
    (hh : ∀ i, CommonBank.headerSlot i ≠ k) (x : ℤ) :
    (CommonBank.bank (SharedBank.empty T prime) hs (fun _ => blank) 0
      (SharedBank.empty 1 prime) (SharedBank.empty 1 prime) c (SharedBank.empty 2 prime)).tape k x = blank := by
  simp only [CommonBank.bank, Shared50RecursiveBank.bank, RecursiveCallBank.bank,
    RecursiveShiftRoleBank.common, SharedBank.empty, RecursiveCallBank.work]
  revert ha hh
  induction k using Fin.addCases with
  | left k => intro _ _; simp [Tapes.append]
  | right k =>
    induction k using Fin.addCases with
    | left k =>
      change Fin (1+6) at k
      induction k using Fin.addCases with
      | left k => intro _ _; simp [Tapes.append]
      | right k => intro _ hh; exact absurd rfl (hh k)
    | right k =>
      induction k using Fin.addCases with
      | right k => intro _ _; simp [Tapes.append]
      | left k =>
        induction k using Fin.addCases with
        | left k => intro _ _; fin_cases k <;> simp [Tapes.append]
        | right k =>
          induction k using Fin.addCases with
          | left k => intro _ _; simp [Tapes.append]
          | right k =>
            induction k using Fin.addCases with
            | left k => intro _ _; simp [Tapes.append]
            | right k => intro ha _; exact absurd rfl (ha k)

/-- Advance across one physical record of the supplier directory, using the
same reciprocal clock as the matrix reader. All remaining entries stay in order. -/
theorem advanceGoodRecord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 6 ↪ Fin T) (m w label : ℕ) (ancestor : ℕ → List (Fin (prime+4)))
    (labels : List ℕ) (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime)
    (stream : S.R (r 2) = ((label :: labels).flatMap (LabelDirectory.entry ancestor m (w+1))) ++ tail)
    (prefixLen : (S.R (r 0)).length = (ancestor label).length) (ticks : (S.R (r 1)).length = w)
    (scratch : S.R (r 3) = []) :
    let rest := labels.flatMap (LabelDirectory.entry ancestor m (w+1)) ++ tail
    ∃ z, z.user = u.user ∧ Exec body (readWithSuccessorClock (r 1) (advanceDirectory m r))
      (mk u S) (1+(4*(ancestor label).length+4+(m*m*(4*(w+1)+4)+1)+1))
      (mk z {S with R := Function.update S.R (r 2) rest}) := by
  intro rest
  let D := {S with R := Function.update S.R (r 1) (Node.tick :: S.R (r 1))}
  have keep (i : Fin 6) (hi : i ≠ 1) : D.R (r i) = S.R (r i) :=
    Function.update_of_ne (r.injective.ne hi) _ _
  have push : Exec body (.act (.push (.rt (r 1)) (fun _ => Node.tick) .done)) (mk u S) 1 (mk u D) := by
    simpa [D,Action.run,update_rt] using Exec.act (body := body) (.push (.rt (r 1)) (fun _ => Node.tick) .done) (mk u S)
  obtain ⟨z,hz,advance⟩ := advanceDirectory_exec body r m (w+1) label (ancestor label) rest u D
    (by rw [keep 2 (by decide),stream]; simp [LabelDirectory.entry,rest,List.append_assoc])
    ((congrArg List.length (keep 0 (by decide))).trans prefixLen) (by simp [D,ticks])
    ((keep 3 (by decide)).trans scratch)
  let E := {D with R := Function.update D.R (r 2) rest}
  have pop := Exec.act (body := body) (Node.dropTop (r 1) .done) (mk z E)
  refine ⟨z,hz,Exec.seq push (Exec.seq advance ?_)⟩
  have restore : Function.update (Function.update S.R (r 2) rest) (r 1) (S.R (r 1)) = Function.update S.R (r 2) rest := by
    funext i; by_cases h : i = r 1 <;> simp [h,r.injective.eq_iff]
  simpa [E,D,Node.dropTop,Action.run,update_rt,Function.update_comm (r.injective.ne (by decide : (1 : Fin 6) ≠ 2)),
    r.injective.eq_iff,restore] using pop

def goodRecordScanPorts : Fin 6 ↪ Fin 7 := ⟨![3,0,1,6,2,5],by decide⟩

open RingFormula LabelTraversal IntegerMultBounds.MathlibTM2.Fast.Main in
theorem generatedRecordScan_exec [M8.Machine.Net] {T m work Q fields H J W : ℕ} {F U : Type}
    (v : Descriptor) (positive : v.Positive) (w : ℕ) (proj : Matrix (Fin m) (Fin m) ℚ)
    (width : v.width = proj.rank*(w+1)) (idem : proj*proj = proj)
    (factor : Factorization univ univ proj) (hd : ∀ a ∈ factorizationDenominators factor, a < prime)
    (rankFits : proj.rank ≤ m) (parent parentInv : Fin m → ZMod (prime^(w+1)))
    (reciprocal : ∀ i, parent i * parentInv i = 1)
    (io : Fin T) (arity : ℕ)
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
    let commonPorts := ((Fin.castAddEmb (n := common) 24).trans (Fin.castAddEmb 31)).trans (Fin.castAddEmb work)
    let aux := (⟨CommonBank.auxSlot,by
      intro i j eq
      apply Fin.ext
      have h := congrArg Fin.val eq
      simp only [CommonBank.auxSlot_val] at h
      omega⟩ : Fin 24 ↪ Fin common).trans commonPorts
    let hdrPorts := (⟨CommonBank.headerSlot,by
      intro i j eq
      apply Fin.ext
      have h := congrArg Fin.val eq
      simp only [CommonBank.headerSlot_val] at h
      omega⟩ : Fin 6 ↪ Fin common).trans commonPorts
    let logical := {v with width := d}
    let addr := fun a row pre mid post (x : IntegerMultBounds.Swap.Shear.State (Fin d) (ZMod M)) =>
      index M logical a row pre (FlatCoordinateLayout.rank x.1).val mid (FlatCoordinateLayout.rank x.2).val post
    let inner := Fin.natAddEmb 66 (m := (host+31)+work)
    let caller := Fin.castAddEmb (n := 66) ((host+31)+work)
    let K := 66+((host+31)+work)
    ∀ (ef : entry.tapes ≤ common+work) (xf : leave.tapes ≤ common+work)
      (eqs : entry.states ≤ Q) (xqs : leave.states ≤ Q) (word : Fin N → ZMod 2) (body : F → Pr F K Q prime U)
      (u : HS _ Q prime U) (whole : Stacks K prime),
      ∀ (poolFits : (conjugationDepth m+1)*13 ≤ work)
        (directory : Descriptor) (prefixes : ℕ → List (Fin (prime+4))) (archiveTail : List (Fin (prime+4))),
      let labels := List.range (LabelMask.records directory)
      let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
      let headers := (Fin.castAddEmb (n := 6) 1).trans slots
      let scanCaller := goodRecordScanPorts.trans slots
      let scan := (scanCaller.trans (Fin.castAddEmb 8)).trans caller
      let joined := recordLoaderBank record
      let dirSlots := goodRecordDirectoryPorts headers
      let dir := dirSlots.trans joined
      let pool := ((Fin.castLEEmb poolFits).trans (Fin.natAddEmb (host+31))).trans inner
      let pivot := goodRecordPivotPorts.trans joined
      let counters := goodRecordCounterPorts.trans joined
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
      let readCost := fun (label : ℕ) => m*(m*(12*(prefixes label).length+8*((w+1)*(m*m))+(w+1)*(7*H+prime+31)+10*H+42)+1)+1
      let generation := fun label => ((1+(readCost label+1)) + (time H (readTime H) detFormula + (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) +
       ((m*(m*(formulaCost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) + (2*(m*m*H)+2))
      let generate : Pr F K Q prime U := (.seq (readWithSuccessorClock clock (directoryMatrix m a digits prefixWidth zeros packedLabel)) (.seq (.seq (.seq (compile (readLeaf (leafBank inputs)) (registerBank pool) detFormula 0 (pivot 14)) (reusablePivotInverse prime pivot clock count))
        (.seq (packedConjugate pool inputs ports false true) (.seq (bclear (pivot 0)) (bclear (pivot 14))))) (bclear packedLabel)))
      let withZero := (Node.umulSym 1 (bitSymbol false) (dir 8) zeros (dir 4)).seq (generate.seq (bclear zeros))
      let field := fun i => caller ((headers i).castAdd 8)
      let slot := (((LeafCore.roleSlot io).castAdd 24).castAdd 31).castAdd work
      let r := recordRoundTripPorts slot
      let src := fun i : Fin 6 => caller ((i.natAdd 33).castLE (by decide : 39 ≤ 66))
      let dst := hdrPorts.trans inner
      let ready := fun (D : Stacks K prime) (pending : List ℕ) =>
        D.R (field 1) = pending.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail ∧
        (∀ j ∈ pending, (D.R (field 3)).length = (prefixes j).length) ∧
        (∀ i : Fin K, 58 ≤ i.val → D.L i = [] ∧ D.R i = []) ∧ D.R (scan 3) = [] ∧
        (∃ suffix, D.R (field 4) = matrixWords prime H (reduce M proj) ++ suffix) ∧
        D.R (caller 2) = binSyms H M ∧ D.R (caller 28) = binSyms 1 1 ∧ D.R (caller 53) = binSyms J W ∧
        (∀ i, D.R (src i) = (Routines.hdr v i).map bitSymbol) ∧
        D.R (caller 44) = binSyms H (1 : ZMod M).val ∧ (D.R (caller 45)).length = w ∧
        D.R (caller 55) = (List.ofFn fun i => binSyms H (parent i).val).flatten
      let payload := fun (word : Fin N → ZMod 2) (D : Stacks K prime) => ∀ z,
        readAt blank (D.L (r 0)) (D.R (r 0)) (z-head) =
          RadixToBinary.binaryEncoding.encode (putWord source head ((List.ofFn word).map SparseRoleCircuit.encode) z)
      let g := physicalLabel m (w+1)
      let G := fun label => g label*reduce M proj*(g label)⁻¹
      let liveBit := LabelStock.live m (w+1) 1
      let badBit := fun label => fallbackBit rankFits (reduce M proj) (g label)
      let call := fun i : Fin d => packedCoordinateProgram (F := Empty) (U := U) io i.val i.val ef xf fits eqs xqs cap
      let cost := packedCoordinatesTime d N w (LeafCore.core io).tapes
        (packedLeafPush (F := Empty) (U := U) io Empty.elim) entry.tapes leave.tapes
      let budget := (d*(4*w+4+columnTime m prime w M.size)+1+(d*(8*(m*m*M.size)+14*M.size+22)+1))+cost
      let coordinate := (goodWeights prime d rankFits bank).seq (Prog.seqList ((List.finRange d).reverse.map call))
      let effect := fun label (word next : Fin N → ZMod 2) =>
        ∃ minor : ∀ k (hk : k < d), IsUnit (GoodForm.lead (k+1) (lt_of_lt_of_le hk rankFits) (G label)).det,
        let stage := GoodForm.stageAt (G label) d rankFits minor d le_rfl
        let pivot := fun i : Fin d => stage.M (i.castLE rankFits) (i.castLE rankFits)
        let weight := fun i : Fin d => parent (i.castLE rankFits)*pivot i
        let inv := fun i : Fin d => parentInv (i.castLE rankFits)*Ring.inverse (pivot i)
        ∀ a < v.beforeRows, ∀ row < v.rows, ∀ pre < v.beforeH, ∀ mid < v.between, ∀ post < v.afterD, ∀ x,
            ext next (addr a row pre mid post (Weighted.child d weight inv x)) = ext word (addr a row pre mid post x)
      let reverse := (Equiv.swap (0 : Fin 8) 1).toEmbedding.trans r
      let transfer := fun ports : Fin 8 ↪ Fin K => (stateLiftNormalize capacity (by decide)).seq
        (stateLiftPr capacity (by decide) Empty.elim (returnFromOrigin (P := Empty) ports))
      let marks := ([2,3,4,5,6,7] : List (Fin 8)).map r
      let packed := (List.ofFn fun i => binSyms (A := prime) M.size (parent i).val).flatten
      let loading := ((6*(m*H)+6)+((10*H+12)+(m*(10*M.size+8*(H-M.size)+12)+1+
        (2*packed.length+2))))+((10*M.size+10)+(6*w+6))
      let conversion := fun label => (m*m)*(10*M.size+8*(H-M.size)+12)+1+(2*(matrixWords prime M.size (G label)).length+2)
      let headerCost := (((List.finRange 6).map fun i => 6*((Routines.hdr v i).length)+6).sum+1)+1
      let runCost := fun label => (((conjugationDepth m+1)*(6*H+6)+1 + (((4*H+4)+(generation label+(2*H+2)))+((conjugationDepth m+1)*(2*H+2)+1))) + (21*(w+1)+13)) + headerCost + ((dimensionTime H 1 fields+(4*(fields*H+1)+6)+(10*J+12)+(6*(M^fields).size+6)) +
        (loading+(conversion label+(budget+2*((218*N+1)*13+6)+3)))) + (1+(4*(prefixes label).length+4+(m*m*(4*(w+1)+4)+1)+1))
      let prepareCounters := (swapExponent (leafCounterPorts aux)).seq
        (.act (installLeafCounters (aux.trans inner) arity d))
      let prepareHeaders := (Record.copyLeafHeaders src dst (caller 64) (caller 65) (List.finRange 6)).seq (.act (pushMarkers ((List.finRange 6).map dst)))
      let recordProgram : Pr F K Q prime U := (((((initFrames pool (pivot 4) (conjugationDepth m+1)).seq (withZero.seq (clearFrames pool (conjugationDepth m+1)))).seq prepareCounters |>.seq prepareHeaders).seq ((recordCounterSetup caller fields).seq ((recordInputProgram record m).seq ((recordMatrixProgram record m).seq ((.act (pushMarkers marks) : Pr F K Q prime U).seq
          ((transfer r).seq ((embProg inner Empty.elim coordinate).seq (transfer reverse)))))))).seq (readWithSuccessorClock (scan 1) (advanceDirectory m scan)))
      let privateTapes := (List.finRange K).filter fun i => decide (58 ≤ i.val)
      let initialClear := privateTapes.length*4+1
      ∀ c, (∀ f, mnProgPush (body f) ≤ c) →
      let charge := fun label => runCost label + (initialClear + 6*(max (mnProgPush recordProgram) c * runCost label))
      let mask := caller 57
      let mode := caller 56
      let modes := fun (js : List ℕ) => js.map (fun i => bitSymbol (a := prime) (badBit i))
      let skip := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
      let skipCost := fun i => 1+(4*(prefixes i).length+4+(m*m*(4*(w+1)+4)+1)+1)
      ∀ (fallback : Pr F K Q prime U) (badCost : ℕ → ℕ) (badEffect : ℕ → (Fin N → ZMod 2) → (Fin N → ZMod 2) → Prop),
      (∀ i is word (u : HS K Q prime U) (S : Stacks K prime), LabelStock.live m (w+1) 1 i = true → fallbackBit rankFits (reduce M proj) (g i) = true → ready S (i :: is) → payload word S →
        ∃ z D n next, z.user = u.user ∧ n ≤ badCost i ∧ Exec body fallback (mk u S) n (mk z D) ∧
          ready D is ∧ badEffect i word next ∧ payload next D ∧ D.R mask = S.R mask ∧ D.R mode = S.R mode) →
      ∀ (rs : List (Pair K)) (parents saved : Fin K) (B : ℕ),
      rs.length = m*m → (parents :: saved :: (LabelTraversal.slots rs ++ [mask])).Nodup →
      (parents :: saved :: (LabelTraversal.slots rs ++ [mode])).Nodup →
      directory.beforeH = B*prime^(m*((w+1)*m)) → LabelTraversal.ready (prime^w) whole.R rs →
      whole.R saved = [] → (whole.R parents).length = directory.beforeRows*directory.rows*B →
      whole.R mask = [] → whole.R mode = [] →
      let clean := {whole with L := fun i => if i ∈ privateTapes then [] else whole.L i,
                               R := fun i => if i ∈ privateTapes then [] else whole.R i}
      ready clean labels → payload word clean →
      let setupCost := 2*((6+10*(m*m))*labels.length+4) +
        ((privateTapes.map fun i => 4*(whole.L i).length+2*(whole.R i).length+4).sum+1)
      let branchCost := fun i => if liveBit i then (if badBit i then badCost i else charge i) else skipCost i
      let action := fun i => if liveBit i then (if badBit i then badEffect i else effect i) else Eq
      ∃ writer : Pr F K Q prime U, ∃ z D n next, z.user = u.user ∧ n ≤ setupCost + ((labels.map fun i => branchCost i + 2 + 4).sum + 2) ∧
        Exec body ((writer.seq (clearWorkTapes privateTapes)).seq (classifiedScan mask mode (recordProgram.seq (clearWorkTapes privateTapes)) fallback skip)) (mk u whole) n (mk z D) ∧
        (ready D [] ∧ D.R mode = modes []) ∧ D.R mask = [] ∧ payload next D ∧
        labels.foldr (fun i rest x => ∃ y, action i x y ∧ rest y) (· = next) word := by
  intro d common host M N entry leave record bank commonPorts aux hdrPorts logical addr inner caller K ef xf eqs xqs initialWord
    body initialUser initialState poolFits directory prefixes archiveTail allLabels slots headers scanCaller scan joined dirSlots dir pool pivot counters inputs ports a digits prefixWidth zeros
    packedLabel clock count formula formulaCost detFormula C readBill generationBill generate withZero field slot r src dst ready payload gs matrices liveBit badBit
    call cost budget coordinate effects reverse transfer marks packed loading conversions headerCost runBills prepareCounters prepareHeaders recordProgram
    privateTapes initialClear c bodyBound charge mask mode modes skip skipCost fallback badCost badEffect bad rs parents saved Bcount sizeRs maskRegs modeRegs shape radix scratch parentCount freeMask freeMode clean initialReady initialPayload setupCost branchCost action
  have clockSlot : headers 0 = 45 := rfl
  have widthSlot : headers 2 = 2 := rfl
  have unitSlot : headers 5 = 44 := rfl
  have scanOff : ∀ i : Fin 6, i < 4 → scanCaller i ≠ 24 := by decide
  have projOff : headers 4 ≠ 24 := by decide
  have dirOff : ∀ j ∈ ([28,53,55] : List (Fin 58)), j ≠ scanCaller 2 := by decide
  have srcOff (i) : src i ≠ scan 2 := by
    intro eq; have h := congrArg Fin.val eq; change 33+i.val = 46 at h; omega
  have release (port : Fin 66) (lo : 56 ≤ port.val) (hi : port.val ≤ 57)
      (is : List ℕ) (word : Fin N → ZMod 2) (S : Stacks K prime) (xs : List (Fin (prime+4)))
      (h : ready S is) (p : payload word S) :
      let B := {S with R := Function.update S.R (caller port) xs}
      ready B is ∧ payload word B := by
    have apart (i : Fin 66) (hi : i ≠ port) : caller i ≠ caller port := caller.injective.ne hi
    have pr (i : Fin K) (hi : 58 ≤ i.val) : i ≠ caller port := by
      intro eq; subst i; change 58 ≤ port.val at hi; omega
    have so (i) : src i ≠ caller port := apart _ (by intro eq; have h := congrArg Fin.val eq; change 33+i.val = port.val at h; omega)
    have right (i : Fin 66) (small : i.val < 56) := Function.update_of_ne (apart i (by intro eq; subst port; omega)) xs S.R
    obtain ⟨hd,hw,hp,hb,hq,h2,h28,h53,hs,h44,h45,h55⟩ := h
    refine ⟨⟨(right 46 (by decide)).trans hd,fun j hj => (congrArg List.length (right 47 (by decide))).trans (hw j hj),
      fun i hi => ⟨(hp i hi).1,(Function.update_of_ne (pr i hi) _ _).trans (hp i hi).2⟩,
      (right 49 (by decide)).trans hb,?_,(right 2 (by decide)).trans h2,(right 28 (by decide)).trans h28,
      (right 53 (by decide)).trans h53,fun i => (Function.update_of_ne (so i) _ _).trans (hs i),
      (right 44 (by decide)).trans h44,(congrArg List.length (right 45 (by decide))).trans h45,
      (right 55 (by decide)).trans h55⟩,?_⟩
    · obtain ⟨suffix,eq⟩ := hq; exact ⟨suffix,(right 48 (by decide)).trans eq⟩
    · intro z
      change readAt _ _ (Function.update S.R (caller port) xs (r 0)) _ = _
      rw [show r 0 = caller 24 from recordRoundTripPorts_other slot 0 (by decide),right 24 (by decide)]
      simpa only [show r 0 = caller 24 from recordRoundTripPorts_other slot 0 (by decide)] using p z
  let liveWords := allLabels.map fun i => bitSymbol (a := prime) (liveBit i)
  let badWords := modes allLabels
  have apart : mask ≠ mode := caller.injective.ne (by decide)
  obtain ⟨writer,generateMasks⟩ := recordMasks_exec body rankFits
    ((LabelRing.res prime (w+1) (by omega)).mapMatrix (reduce M proj)) rs sizeRs mask mode parents saved apart maskRegs modeRegs
  obtain ⟨y,l,hy,hl,write⟩ := generateMasks directory w Bcount (reduce M proj) rfl shape initialUser initialState
    radix scratch parentCount freeMask freeMode
  obtain ⟨z,hz,clearMasks⟩ := clearAfterMasks_exec body mask mode privateTapes ((List.nodup_finRange K).filter _)
    (by simp [privateTapes,mask,caller]) (by simp [privateTapes,mode,caller]) liveWords badWords y initialState
  let liveState := {clean with R := Function.update clean.R mask liveWords}
  let startState := {liveState with R := Function.update liveState.R mode badWords}
  obtain ⟨r₁,p₁⟩ := release 57 (by decide) (by decide) _ _ clean liveWords initialReady initialPayload
  obtain ⟨r₂,p₂⟩ := release 56 (by decide) (by decide) _ _ liveState badWords r₁ p₁
  have bits : startState.R mask = liveWords := (Function.update_of_ne apart badWords liveState.R).trans
    (Function.update_self mask liveWords clean.R)
  have initialModes : startState.R mode = badWords := Function.update_self mode badWords liveState.R
  suffices scanRun : ∃ finish D n next, finish.user = z.user ∧
      n ≤ (allLabels.map fun i => branchCost i+2+4).sum+2 ∧
      Exec body (classifiedScan mask mode (recordProgram.seq (clearWorkTapes privateTapes)) fallback skip)
        (mk z startState) n (mk finish D) ∧ (ready D [] ∧ D.R mode = modes []) ∧ D.R mask = [] ∧ payload next D ∧
      allLabels.foldr (fun i rest x => ∃ y, action i x y ∧ rest y) (· = next) initialWord by
    obtain ⟨finish,D,n,next,user,time,run,post⟩ := scanRun
    exact ⟨writer,finish,D,_,next,user.trans (hz.trans hy),Nat.add_le_add (Nat.add_le_add_right hl _) time,
      Exec.seq (Exec.seq write clearMasks) run,post⟩
  apply classifiedPayloadScan_exec body mask mode (caller.injective.ne (by decide)) _ fallback skip liveBit badBit
    branchCost (fun is D => ready D is) payload action _ _ allLabels initialWord z startState
    r₂ p₂ bits initialModes
  · intro k hk
    rcases hk with rfl | rfl
    · exact release 57 (by decide) (by decide)
    · exact release 56 (by decide) (by decide)
  · intro label labels word u whole start input
    by_cases live : liveBit label = true
    case neg =>
      have pad := Bool.eq_false_iff.mpr live
      obtain ⟨dir,widths,privateBlank,scratch,projector,base,unit,trailing,headersIn,one,ticks,archive⟩ := start
      let tail := labels.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail
      obtain ⟨z,user,advance⟩ := advanceGoodRecord_exec body scan m w label prefixes labels archiveTail u whole dir
        (widths label List.mem_cons_self) ticks scratch
      let D := {whole with R := Function.update whole.R (scan 2) tail}
      have keep (j : Fin 66) (hj : j ≠ 46) : D.R (caller j) = whole.R (caller j) :=
        Function.update_of_ne (caller.injective.ne hj) _ _
      have rdy : ready D labels := by
        refine ⟨(show D.R (field 1) = tail from Function.update_self (scan 2) tail whole.R),fun j hj => (congrArg List.length (keep 47 (by decide))).trans
          (widths j (List.mem_cons_of_mem _ hj)),?_,(keep 49 (by decide)).trans scratch,?_,
          (keep 2 (by decide)).trans base,(keep 28 (by decide)).trans unit,(keep 53 (by decide)).trans trailing,
          fun i => (Function.update_of_ne (srcOff i) _ _).trans (headersIn i),(keep 44 (by decide)).trans one,
          (congrArg List.length (keep 45 (by decide))).trans ticks,(keep 55 (by decide)).trans archive⟩
        · intro i hi
          exact ⟨(privateBlank i hi).1,(Function.update_of_ne (by intro eq; subst i; change 58 ≤ 46 at hi; omega) _ _).trans (privateBlank i hi).2⟩
        · obtain ⟨xs,h⟩ := projector; exact ⟨xs,(keep 48 (by decide)).trans h⟩
      have pay : payload word D := by
        intro k
        have port := recordRoundTripPorts_other slot 0 (by decide)
        change readAt _ (whole.L (r 0)) (D.R (r 0)) _ = _
        rw [show r 0 = caller 24 from port,keep 24 (by decide)]
        simpa only [show r 0 = caller 24 from port] using input k
      simp only [branchCost,action,pad,Bool.false_eq_true,ite_false]
      exact ⟨z,D,_,word,user,le_rfl,advance,rdy,rfl,pay,keep 57 (by decide),keep 56 (by decide)⟩
    by_cases fail : badBit label = true
    · simpa only [branchCost,action,live,fail,ite_true] using bad label labels word u whole live fail start input
    have good := Bool.eq_false_iff.mpr fail
    simp only [branchCost,action,live,good,Bool.false_eq_true,ite_false,ite_true]
    let g := gs label
    let G := matrices label
    let ancestor := prefixes label
    let tail := labels.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ archiveTail
    let readCost := readBill label
    let generation := generationBill label
    let conversion := conversions label
    let runCost := runBills label
    obtain ⟨dirInput,widths,privateBlank,scanBlank,projectorInput,base,unit,trailing,sourceWords,one,ticks,archive⟩ := start
    have prefixInput := widths label List.mem_cons_self
    let commonTape := fun k : Fin common => (((k.castAdd 24).castAdd 31).castAdd work)
    let roles := SharedBank.empty T prime
    let node := SharedBank.empty 1 prime
    let scalar := SharedBank.empty 1 prime
    let st := SharedBank.empty 2 prime
    let f := fun _ : ℤ => (blank : Fin (prime+4))
    let p := (0 : ℤ)
    let initialBank := CommonBank.bank roles (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d d) st
    let S := embStk inner whole
    have freeNode : Family.NodeFree node := fun _ _ => rfl
    have innerBlank (j) := privateBlank (inner j) (show 58 ≤ 66+j.val by omega)
    have spare (i : Fin 66) (hi : 58 ≤ i.val) := privateBlank (caller i) hi
    have hdrBlank (i) := innerBlank (hdrPorts i)
    have auxBlank (i) := innerBlank (aux i)
    have sharedBlank (z : ℤ) : readAt blank (whole.L (r 1)) (whole.R (r 1)) z = blank := by
      rw [show r 1 = inner slot from recordRoundTripPorts_shared slot,(innerBlank slot).1,(innerBlank slot).2,
        readAt_nil_left,wordTape_nil]
    have workBlank (k : Fin work) := innerBlank (k.natAdd (host+31))
    have poolBlank (j) : whole.R (pool j) = [] := (workBlank ((Fin.castLEEmb poolFits) j)).2
    have free : ∀ (k : Fin work) x,
        readAt blank (S.L (k.natAdd (host+31))) (S.R (k.natAdd (host+31))) x = blank := by
      intro k x
      change readAt _ (whole.L _) (whole.R _) _ = _
      rw [(workBlank k).1, (workBlank k).2,readAt_nil_left,wordTape_nil]
    have empty (k : Fin 31) := innerBlank ((k.natAdd host).castAdd work)
    have scratch (i : Fin 24) (_ : i ≠ 16) := (innerBlank (record i)).2
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
        let scratchSlots : Fin 12 → Fin 24 := ![2,3,4,5,6,7,17,8,9,10,11,18]
        have allSlots (l : Fin (6+12)) :
            finSumFinEquiv (Sum.map headers scratchSlots (finSumFinEquiv.symm l)) ≠ goodRecordPivotPorts j := by
          induction l using Fin.addCases with
          | left k =>
            rw [finSumFinEquiv_symm_apply_castAdd]
            exact (by decide : ∀ k : Fin 58, ∀ j ∈ ([0,1,12,14] : List (Fin 16)), k.castAdd 24 ≠ goodRecordPivotPorts j) (headers k) j hj
          | right k =>
            rw [finSumFinEquiv_symm_apply_natAdd]
            exact (by decide : ∀ k : Fin 12, ∀ j ∈ ([0,1,12,14] : List (Fin 16)),
            ((![2,3,4,5,6,7,17,8,9,10,11,18] k : Fin 24).natAdd 58) ≠ goodRecordPivotPorts j) k j hj
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
    have header (i : Fin 6) : joined ((headers i).castAdd 24) = field i := recordLoaderBank_caller record (headers i)
    have directoryWord : whole.R (dir 2) = ancestor ++ (LabelDirectory.digits m (w+1) label).map RadixDigits.digitSymbol ++ tail := by
      change whole.R (joined ((headers 1).castAdd 24)) = _
      simpa only [ancestor,tail,List.flatMap_cons,LabelDirectory.entry,List.append_assoc] using
        (congrArg whole.R (header 1)).trans dirInput
    have prefixLen := (congrArg (fun i => (whole.R i).length) (header 3)).trans prefixInput
    have fieldClock : dir 1 = clock := by
      change joined ((headers 0).castAdd 24) = joined 45
      rw [clockSlot]; rfl
    have projector : ∃ suffix, whole.R (dir 16) = matrixWords prime H (reduce M proj) ++ suffix := by
      change ∃ suffix, whole.R (joined ((headers 4).castAdd 24)) = _
      rwa [header]
    have packedEmpty := dirEmpty 10 (by decide)
    have widthPort : dir 8 = caller 2 := by
      change joined ((headers 2).castAdd 24) = _
      rw [widthSlot]; exact recordLoaderBank_caller record 2
    have unitPort : dir 17 = caller 44 := by
      change joined ((headers 5).castAdd 24) = _
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
      withZero (matrixWords prime H G) ((4*H+4)+(generation+(2*H+2))) u whole poolBlank (by
      intro v' E stable filled frames
      have widthE : (E.R (dir 8)).length = H := (congrArg List.length (stable _ (bp 8))).trans digitWidth
      let Z := {E with R := Function.update E.R zeros (binSyms (A := prime) H 0)}
      have zeroWord : Z.R zeros = binSyms H 0 := Function.update_self ..
      have dirKeep (i : Fin 18) (hi : i ≠ 9) : Z.R (dir i) = whole.R (dir i) :=
        (Function.update_of_ne (dir.injective.ne hi) _ _).trans (stable _ (bp i))
      apply (by
        simpa only [widthE] using withRecordZero_exec body (dir 8) zeros (dir 4) out
          (by change [dir 8,dir 9,dir 4].Nodup; simp) (joined.injective.ne (by decide : (74 : Fin 82) ≠ 76))
          generate (matrixWords prime H G) generation v' E ((stable _ (bp 9)).trans (regEmpty 18 (by decide)))
          ((stable _ (bp 4)).trans (dirEmpty 4 (by decide))) : _ → _)
      intro vZero
      let R := Function.update Z.R packedLabel (matrixWords prime H g)
      have updated (i) (hi : ∀ j, i ≠ pool j) (nz : i ≠ zeros) (ne : packedLabel ≠ i) : R i = whole.R i :=
        (Function.update_of_ne ne.symm _ _).trans ((Function.update_of_ne nz _ _).trans (stable i hi))
      have pivotKept (i) := updated (pivot i) (rp i) (joined.injective.ne ((by decide : ∀ i, goodRecordPivotPorts i ≠ 76) i)) (br 10 i (Or.inl rfl))
      have keep (i : Fin 18) (hi : i ≠ 10) (nz : i ≠ 9) : R (dir i) = whole.R (dir i) :=
        (Function.update_of_ne (dir.injective.ne hi) _ _).trans (dirKeep i nz)
      let sources := QueueLayout.formulaInputs.trans dir
      have matrices (b : Bool) : ∃ suffix, R (sources (if id b then 7 else 2)) = matrixWords prime H (mat b) ++ suffix := by
        cases b
        · exact ⟨[],by simp [R,sources,QueueLayout.formulaInputs,packedLabel,mat]⟩
        · change ∃ suffix, R (dir 16) = matrixWords prime H (reduce M proj) ++ suffix
          rwa [keep 16 (by decide) (by decide)]
      have leaves := sourcePorts_ready sources id mat H R matrices
        ((congrArg List.length (keep 8 (by decide) (by decide))).trans digitWidth)
        (show R (dir 9) = _ from (Function.update_of_ne (dir.injective.ne (by decide : (9 : Fin 18) ≠ 10)) _ _).trans zeroWord) ((keep 17 (by decide) (by decide)).trans inputOne)
        (fun i hi => by
          have ok := (by decide : ∀ i ∈ ([0,4,5,6] : List (Fin 10)), ∃ j : Fin 7,
            (j = 0 ∨ 3 ≤ j) ∧ QueueLayout.formulaInputs i = QueueLayout.directoryWork (QueueLayout.readPorts j) ∧
            QueueLayout.formulaInputs i ≠ 10) i hi
          obtain ⟨j,hj,eq,ne⟩ := ok
          exact (keep _ ne ((by decide : ∀ i ∈ ([0,4,5,6] : List (Fin 10)), QueueLayout.formulaInputs i ≠ 9) i hi)).trans ((congrArg whole.R (congrArg dir eq)).trans (freeRead j hj)))
      have scratchPort : ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 →
          QueueLayout.normalizationPorts k ≠ 4 ∧ QueueLayout.normalizationPorts k < 13 := by decide
      have posH : 0 < H := by
        have hp := pow_pos Networks.Shared50ModularControl.prime_prime.pos (w+1)
        by_contra! h
        rw [show H = 0 by omega,pow_zero] at hm
        omega
      have readMatrix := directoryMatrix_writes body a digits rfl
        (fun i j => ((by decide : ∀ i j, QueueLayout.readPorts i ≠ QueueLayout.digitPorts j ∨ i = 3 ∧ j = 0) i j).imp
          (fun h => (QueueLayout.directoryWork.trans dir).injective.ne h) id)
        prefixWidth zeros packedLabel (by change [dir 12,dir 0,dir 6].Nodup; simp)
        (by change [dir 12,dir 9,dir 10].Nodup; simp) (dir.injective.ne (by decide : (12 : Fin 18) ≠ 7))
        (fun i => dir.injective.ne ((by decide : ∀ i, QueueLayout.directoryWork (QueueLayout.readPorts i) ≠ 10) i))
        (fun i => dir.injective.ne ((by decide : ∀ i, QueueLayout.directoryWork (QueueLayout.digitPorts i) ≠ 10) i))
        (fun i => dir.injective.ne ((by decide : ∀ i, 9 ≠ QueueLayout.directoryWork (QueueLayout.digitPorts i)) i)) m (w+1) label H posH ancestor tail
      have read := readWithSuccessorClock_writes body clock packedLabel clockOff.symm _ _ _ _ readMatrix
      have keepRead (i : Fin 18) (hi : i ≠ 1) :
          Function.update Z.R clock (Node.tick :: Z.R clock) (dir i) = Z.R (dir i) := by
        rw [← fieldClock]; exact Function.update_of_ne (dir.injective.ne hi) _ _
      have zClock : (Z.R clock).length = w := by
        rw [← fieldClock]
        exact (congrArg List.length (dirKeep 1 (by decide))).trans (by rw [fieldClock]; exact clockWidth)
      have gen := physicalConjugationFromReader_writes body w label mat false true rfl live pivot clock count copyPorts
        (fun i => rc i 1) (rc 14 0).symm H hm pool inputs (fun _ _ j => bp _ j) ports
        (fun k => (rp 14 k).symm) (fun _ _ => br _ 14 (Or.inr (by decide))) (fun k => (rp 0 k).symm) (fun _ _ => br _ 0 (Or.inr (by decide)))
        (fun j => pivot.injective.ne ((by decide : ∀ j, QueueLayout.normalizationPorts j ≠ 14) j)) rfl
        (fun k _ _ => (rp _ k).symm) packedLabel (br 10 13 (Or.inl rfl)) _ _ _ read
        (fun _ _ j hj => br _ _ (Or.inr ((by decide : ∀ j : Fin 14, j = 1 ∨ j = 13 →
          QueueLayout.normalizationPorts j ∈ ([0,1,12,14] : List (Fin 16))) j hj)))
        depthFits (Nat.le_max_left _ _) vZero Z
        ⟨by
            exact ⟨(keepRead 2 (by decide)).trans ((dirKeep _ (by decide)).trans directoryWord),
              (congrArg List.length (keepRead 12 (by decide))).trans ((congrArg List.length (dirKeep _ (by decide))).trans prefixLen),
              by change ((Function.update Z.R clock (Node.tick :: Z.R clock)) (dir 1)).length = w+1
                 rw [fieldClock,Function.update_self,List.length_cons,zClock],
              fun i hi => (keepRead _ ((by decide : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i → QueueLayout.directoryWork (QueueLayout.readPorts i) ≠ 1) i hi)).trans
                ((dirKeep _ ((by decide : ∀ i : Fin 7, QueueLayout.directoryWork (QueueLayout.readPorts i) ≠ 9) i)).trans (freeRead i hi)),
              (congrArg List.length (keepRead 8 (by decide))).trans ((congrArg List.length (dirKeep _ (by decide))).trans digitWidth),
              fun i hi => (keepRead _ ((by decide : ∀ i : Fin 6, QueueLayout.directoryWork (QueueLayout.digitPorts i) ≠ 1) i)).trans
                ((dirKeep _ ((by decide : ∀ i : Fin 6, QueueLayout.directoryWork (QueueLayout.digitPorts i) ≠ 9) i)).trans (freeDigit i hi)),
              (keepRead 9 (by decide)).trans zeroWord⟩,
          (dirKeep _ (by decide)).trans packedEmpty,(congrArg List.length (updated clock (cp 0) (joined.injective.ne (by decide : (45 : Fin 82) ≠ 76)) clockOff)).trans clockWidth,
          (updated count (cp 1) (joined.injective.ne (by decide : (73 : Fin 82) ≠ 76)) countOff).trans (regEmpty 15 (by decide)),(pivotKept 14).trans (pivotEmpty 14 (by decide)),(pivotKept 15).trans unitWord,
          (pivotKept 4).trans modulusWord,fun i h l => (pivotKept i).trans (pivotEmpty i (Or.inl ⟨h,l⟩)),
          fun k hk => (Function.update_of_ne (bp 10 _).symm _ _).trans ((Function.update_of_ne (bp 9 _).symm _ _).trans ((filled k hk).trans modulusWord)),
          fun k hk i hi => (Function.update_of_ne (bp 10 _).symm _ _).trans ((Function.update_of_ne (bp 9 _).symm _ _).trans (frames k hk i hi)),leaves,
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
    let auxPort := aux.trans inner
    have commonKeep (i : Fin common) : B.R (inner (commonTape i)) = whole.R (inner (commonTape i)) :=
      privateKept _ (Or.inl i.isLt)
    have auxEmpty (i : Fin 24) : B.L (auxPort i) = [] ∧ B.R (auxPort i) = [] :=
      ⟨(auxBlank i).1,(commonKeep (CommonBank.auxSlot i)).trans (auxBlank i).2⟩
    obtain ⟨counterUser,E,costC,hUser,hCost,prep,auxRep,auxKeep⟩ :=
      prepareLeafCounters_exec body auxPort (leafCounterPorts aux) rfl arity d w y B
        ((congrArg List.length (preserved 45)).trans ticks)
        (by intro i hi; cases i using Fin.cases with
            | zero => exact (hi rfl).elim
            | succ j => exact (auxEmpty (j.castLE (by decide))).2) auxEmpty
    have callerApart (i : Fin 66) (j) : caller i ≠ dst j := by
      intro eq; have h := congrArg Fin.val eq
      change i.val = 66+(hdrPorts j).val at h; omega
    have srcApart (i j) : src i ≠ dst j := callerApart _ _
    have callerE (i : Fin 66) := auxKeep (caller i) (by
      intro j eq; have h := congrArg Fin.val eq
      change 66+(aux j).val = i.val at h; omega)
    have hdrNe (i j) : CommonBank.auxSlot (t := T) i ≠ CommonBank.headerSlot j := by
      intro eq; have h := congrArg Fin.val eq
      rw [CommonBank.auxSlot_val, CommonBank.headerSlot_val] at h
      have := j.isLt
      omega
    have dstE (j) := auxKeep (dst j) (fun i eq => hdrNe i j (commonPorts.injective (inner.injective eq)))
    have wordsE (i) : E.R (src i) = (Routines.hdr v i).map bitSymbol :=
      (callerE _).2.trans ((preserved _).trans (sourceWords i))
    obtain ⟨headerUser,C,hHeaders,install,hdrRep,hdrKeep⟩ := prepareRecordHeaders_exec body v src dst
      (caller 64) (caller 65) srcApart (by
        intro i
        simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or]
        exact ⟨⟨srcApart i i,by intro eq; have h := congrArg Fin.val eq; change 33+i.val = 64 at h; omega,
          by intro eq; have h := congrArg Fin.val eq; change 33+i.val = 65 at h; omega⟩,
          ⟨(callerApart 64 i).symm,(callerApart 65 i).symm⟩,caller.injective.ne (by decide),by simp⟩)
      counterUser E wordsE (fun j => ⟨(dstE j).1.trans (hdrBlank j).1,
        (dstE j).2.trans ((commonKeep (CommonBank.headerSlot j)).trans (hdrBlank j).2)⟩)
      ((callerE 64).2.trans ((preserved 64).trans (spare 64 (by decide)).2))
      ((callerE 65).2.trans ((preserved 65).trans (spare 65 (by decide)).2))
    simp only [wordsE,List.length_map] at install
    have keep (j) (ha : ∀ i, auxPort i ≠ j) (hh : ∀ i, dst i ≠ j) :=
      And.intro ((hdrKeep j hh).1.trans (auxKeep j ha).1) ((hdrKeep j hh).2.trans (auxKeep j ha).2)
    have callerFrame (i : Fin 66) := And.intro
      ((hdrKeep _ (fun j => (callerApart i j).symm)).1.trans (callerE i).1)
      ((hdrKeep _ (fun j => (callerApart i j).symm)).2.trans (callerE i).2)
    have commonOff (k : Fin common) (j) (hj : common ≤ j.val) : inner (commonTape k) ≠ inner j := by
      intro eq; have h := congrArg Fin.val (inner.injective eq)
      change k.val = j.val at h; omega
    have outsideCommon (j) (hj : common ≤ j.val) := keep (inner j) (fun _ => commonOff _ j hj) (fun _ => commonOff _ j hj)
    have other (k : Fin common) (ha : ∀ i, CommonBank.auxSlot i ≠ k) (hh : ∀ i, CommonBank.headerSlot i ≠ k) :=
      keep (inner (commonTape k)) (fun i eq => ha i (commonPorts.injective (inner.injective eq)))
        (fun i eq => hh i (commonPorts.injective (inner.injective eq)))
    have roleKeep := other (LeafCore.roleSlot io) (by
      intro i eq; have h := congrArg Fin.val eq
      rw [CommonBank.auxSlot_val] at h
      change T+12+i.val = io.val at h; omega) (by
      intro i eq; have h := congrArg Fin.val eq
      rw [CommonBank.headerSlot_val] at h
      change T+1+i.val = io.val at h; omega)
    obtain ⟨z,D,t,ys,hz,ht,run,act,read,frame⟩ := goodRecordRoundTrip_exec
      v positive w proj width idem factor hd label live rankFits parent parentInv reciprocal io roles f p node scalar
      arity st freeNode hm hw hW length capacity source head fits cap ef xf eqs xqs word body headerUser C (whole.R out)
      ((callerFrame 2).2.trans ((preserved 2).trans base)) ((callerFrame 28).2.trans ((preserved 28).trans unit))
      ((callerFrame 53).2.trans ((preserved 53).trans trailing))
      (fun i hi => ⟨(callerFrame i).1.trans (spare i hi).1,(callerFrame i).2.trans ((preserved i).trans (spare i hi).2)⟩)
      (by intro z; change readAt _ (C.L (r 0)) (C.R (r 0)) _ = _
          rw [first,(callerFrame 24).1,(callerFrame 24).2,preserved]; simpa only [first] using input z)
      (by intro z; change readAt _ (C.L (r 1)) (C.R (r 1)) _ = _
          rw [← shared,show C.L (inner slot) = B.L (inner slot) from roleKeep.1,
            show C.R (inner slot) = B.R (inner slot) from roleKeep.2,privateKept _ (Or.inl (LeafCore.roleSlot io).isLt)]
          simpa only [← shared] using sharedBlank z)
      (by intro k x
          change initialBank.tape k x = readAt _ (C.L (inner (commonTape k))) (C.R (inner (commonTape k))) _
          by_cases h : ∃ i, CommonBank.auxSlot i = k
          · obtain ⟨i,rfl⟩ := h
            have atAux := CommonBank.bank_aux roles (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d d) st i
            change _ = readAt _ _ _ (x-initialBank.head _)
            rw [show initialBank.head _ = _ from atAux.1, show initialBank.tape _ = _ from atAux.2]
            have kept := hdrKeep (auxPort i) (fun j eq => hdrNe i j (commonPorts.injective (inner.injective eq.symm)))
            change _ = readAt _ (C.L (auxPort i)) (C.R (auxPort i)) _
            rw [kept.1,kept.2]
            exact auxRep i x
          · by_cases hh : ∃ i, CommonBank.headerSlot i = k
            · obtain ⟨i,rfl⟩ := hh
              have facts := CommonBank.bank_header roles (Routines.hdr v) f p node scalar (Family.leafC (w+1) arity d d) st i
              rw [show initialBank.head _ = _ from facts.1,show initialBank.tape _ = _ from facts.2]
              exact hdrRep i x
            · have off := other k (fun i eq => h ⟨i,eq⟩) (fun i eq => hh ⟨i,eq⟩)
              rw [off.1,off.2,commonKeep,show B.L _ = [] from (innerBlank (commonTape k)).1,
                (innerBlank (commonTape k)).2,readAt_nil_left,wordTape_nil]
              exact emptyCommonTape _ _ k (fun i eq => h ⟨i,eq⟩) (fun i eq => hh ⟨i,eq⟩) x)
      (by intro k x
          let j := k.natAdd (host+31)
          have hi : host ≤ j.val := by simp [j]; omega
          change readAt _ (C.L (inner j)) (C.R (inner j)) _ = _
          rw [(outsideCommon j (by dsimp [host] at hi; omega)).1,(outsideCommon j (by dsimp [host] at hi; omega)).2,
            privateKept _ (Or.inr hi)]
          exact free k x)
      (fun k => by
        let j := (k.natAdd host).castAdd work
        have hi : host ≤ j.val := by simp [j]
        have off := outsideCommon j (by dsimp [host] at hi; omega)
        exact ⟨off.1.trans (empty k).1,off.2.trans ((privateKept j (Or.inr hi)).trans (empty k).2)⟩)
      good (by change C.R out = _
               rw [show C.R out = B.R out from (outsideCommon (record 16) (by change common ≤ common+16; omega)).2]
               simp [B,G,matrices,gs,M])
      ((callerFrame 44).2.trans ((preserved 44).trans one))
      ((congrArg List.length (callerFrame 45).2).trans ((congrArg List.length (preserved 45)).trans ticks))
      ((callerFrame 55).2.trans ((preserved 55).trans archive))
      (by intro i hi
          exact (outsideCommon (record i) (by change common ≤ common+i.val; omega)).2.trans
            ((Function.update_of_ne (inner.injective.ne (record.injective.ne hi)) _ _).trans (scratch i hi)))
    have keptCaller (j : Fin 58) (ne : j ≠ 24) :=
      (frame j ne).2.trans ((callerFrame _).2.trans (preserved _))
    have keptScan (i : Fin 6) (hi : i < 4) : D.R (scan i) = whole.R (scan i) :=
      keptCaller _ (scanOff i hi)
    obtain ⟨last,user,advance⟩ := advanceGoodRecord_exec body scan m w label prefixes labels archiveTail z D
      ((keptScan 2 (by decide)).trans dirInput)
      ((congrArg List.length (keptScan 0 (by decide))).trans prefixInput)
      ((congrArg List.length (keptScan 1 (by decide))).trans (show (whole.R (field 0)).length = w by
        change (whole.R (caller ((headers 0).castAdd 8))).length = _
        rw [clockSlot]; exact ticks))
      ((keptScan 3 (by decide)).trans scanBlank)
    let finalBank := {D with R := Function.update D.R (scan 2) tail}
    have step : Exec body recordProgram (mk u whole) _ (mk last finalBank) :=
      Exec.seq (Exec.seq (Exec.seq (Exec.seq runWriter prep) install) run) advance
    have bound : (n+costC+headerCost)+t+(1+(4*ancestor.length+4+(m*m*(4*(w+1)+4)+1)+1)) ≤ runCost := by
      apply Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hn hCost) _) _) _
      rw [show C.R ((Fin.castAddEmb (CommonBank.count T+24+31+work)) 55) = whole.R (caller 55) from (callerFrame 55).2.trans (preserved 55),
        show C.R ((Fin.castAddEmb (CommonBank.count T+24+31+work)) 45) = whole.R (caller 45) from (callerFrame 45).2.trans (preserved 45)] at ht
      rw [archive,ticks] at ht
      simpa [loading,packed,List.length_flatten,Function.comp_def,length_binSyms,List.ofFn_const] using ht
    have distinct : privateTapes.Nodup := (List.nodup_finRange K).filter _
    obtain ⟨finish,userFinish,clear⟩ := clearWorkTapes_exec body privateTapes distinct last finalBank
    have charge := recordCleanup_cost_le privateTapes distinct step (le_max_left (mnProgPush recordProgram) c)
      (fun f => (bodyBound f).trans (le_max_right _ _))
    have privateMem (i : Fin K) : i ∈ privateTapes ↔ 58 ≤ i.val := by simp [privateTapes]
    have init : (privateTapes.map fun i => 4*(whole.L i).length+2*(whole.R i).length+4) =
        privateTapes.map (fun _ => 4) := by
      apply List.map_congr_left
      intro i hi
      simp [privateBlank i ((privateMem i).mp hi)]
    simp only [init,List.map_const',List.sum_replicate_nat] at charge
    have callerOut (j : Fin 58) : caller (j.castAdd 8) ∉ privateTapes := by
      rw [privateMem]; exact Nat.not_le_of_lt j.isLt
    have payloadOut : r 0 ∉ privateTapes := by rw [first]; exact callerOut 24
    have finalFrame (j : Fin 58) (ne : j ≠ 24) (nd : j ≠ scanCaller 2) :
        let port := caller (j.castAdd 8)
        (if port ∈ privateTapes then [] else finalBank.L port) = whole.L port ∧
          (if port ∈ privateTapes then [] else finalBank.R port) = whole.R port := by
      have off : caller (j.castAdd 8) ≠ scan 2 := caller.injective.ne ((Fin.castAddEmb 8).injective.ne nd)
      simp only [ite_eq_right (callerOut j)]
      exact ⟨(frame j ne).1.trans (callerFrame _).1,(Function.update_of_ne off _ _).trans (keptCaller j ne)⟩
    have hdrFrame (i : Fin 6) (hp : headers i ≠ 24) (hd : i ≠ 1) :=
      (finalFrame (headers i) hp (headers.injective.ne hd)).2
    obtain ⟨minor,next,rfl,action⟩ := act
    refine ⟨finish,_,_,next,userFinish.trans (user.trans (hz.trans (hHeaders.trans (hUser.trans hy)))),Nat.add_le_add bound
      (charge.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left _ bound)) _)),
      Exec.seq step clear,?_,⟨minor,action⟩,?_,(finalFrame 57 (by decide) (by decide)).2,(finalFrame 56 (by decide) (by decide)).2⟩
    · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · simp [show scan 2 ∉ privateTapes from callerOut _,finalBank,show field 1 = scan 2 from rfl,tail]
      · intro j hj
        exact (congrArg List.length (hdrFrame 3 (scanOff 0 (by decide)) (by decide))).trans
          (widths j (List.mem_cons_of_mem _ hj))
      · intro i hi; simp [(privateMem i).mpr hi]
      · exact (finalFrame (scanCaller 3) (scanOff 3 (by decide)) (scanCaller.injective.ne (by decide))).2.trans scanBlank
      · obtain ⟨xs,h⟩ := projectorInput
        exact ⟨xs,(hdrFrame 4 projOff (by decide)).trans h⟩
      · have h := hdrFrame 2 (by rw [widthSlot]; decide) (by decide)
        rw [widthSlot] at h; exact h.trans base
      · exact (finalFrame 28 (by decide) (dirOff 28 (by decide))).2.trans unit
      · exact (finalFrame 53 (by decide) (dirOff 53 (by decide))).2.trans trailing
      · intro i
        let j : Fin 58 := (i.natAdd 33).castLE (by decide : 39 ≤ 58)
        have ne : j ≠ 24 := by intro eq; have h := congrArg Fin.val eq; change 33+i.val = 24 at h; omega
        exact (finalFrame j ne (fun eq => srcOff i (congrArg (fun k : Fin 58 => caller (k.castAdd 8)) eq))).2.trans (sourceWords i)
      · have h := hdrFrame 5 (by rw [unitSlot]; decide) (by decide)
        rw [unitSlot] at h; exact h.trans one
      · have h := hdrFrame 0 (by rw [clockSlot]; decide) (by decide)
        rw [clockSlot] at h; exact (congrArg List.length h).trans ticks
      · exact (finalFrame 55 (by decide) (dirOff 55 (by decide))).2.trans archive
    · have off : r 0 ≠ scan 2 := by
        rw [first]
        exact caller.injective.ne ((Fin.castAddEmb 8).injective.ne (scanOff 2 (by decide)).symm)
      simpa only [payload,ite_eq_right payloadOut,finalBank,Function.update_of_ne off] using read


end IntegerMultBounds.MathlibTM2.Cover.Fallback
