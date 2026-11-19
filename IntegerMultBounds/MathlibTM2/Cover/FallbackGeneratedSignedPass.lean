module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalSignedPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugationQueue
public import IntegerMultBounds.MathlibTM2.Cover.FallbackIdentitySeed

/-! Compose residual queue generation and the signed pass on their shared archive register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable [M8.Machine.Net] {T K Q d r w W : ℕ} {P U : Type}
local notation "N" => rowSwapBlock.tapes+35

open Record RecursiveInterchangeLayout RingFormula Node
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨pow_ne_zero _ Networks.Shared50ModularControl.prime_prime.ne_zero⟩

noncomputable def seededQueueBody (r d : ℕ) (e : (Fin r ⊕ Fin r) ≃ Fin (d+1))
    (bank : Fin 18 ↪ Fin K) (recip : Fin 16 ↪ Fin K) (clock count : Fin K)
    (pool : Fin ((conjugationDepth r+1)*13) ↪ Fin K) (coeff : Fin r → Fin r → Fin 4 ↪ Fin K)
    (coeffOff : ∀ i j k l, recip k ≠ coeff i j l) (scan : Fin 6 ↪ Fin K)
    (mask seed tmp : Fin K) : Pr P K Q prime U :=
  let inputs := QueueLayout.formulaInputs.trans bank
  let source := sourcePorts (m := r) inputs id
  let weights := fun i j => QueueLayout.residualPorts recip (coeff i j) (coeffOff i j)
  let f := determinant (matrixInput false)
  let conjugate : Pr P K Q prime U := (.seq (directoryMatrix r (QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans bank)) (QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans bank)) (bank 12) (bank 9) (bank 10)) (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (recip 14)) (reusablePivotInverse prime recip clock count))
        (.seq (packedConjugate pool source (QueueLayout.normalizationPorts.trans recip) false true) (.seq (bclear (recip 0)) (bclear (recip 14))))) (bclear (bank 10))))
  let live : Pr P K Q prime U := .seq conjugate (.seq (sequence (fun i => sequence
      (fun j => blockEntry weights (e.symm i) (e.symm j)) (List.finRange (d+1))) (List.finRange (d+1))) (bclear (recip 13)))
  let branch := fun p => Prog.seq p (.seq (moveR (scan 4) (scan 5) id) (advanceDirectory r scan))
  (.seq (maskedScan mask (branch live) (branch (bcopy seed (scan 4) (scan 3) tmp)))
        (moveR (scan 5) (scan 4) id))

noncomputable def withIdentitySeed (d : ℕ) (zero one seed tmp saved : Fin K) (generate : Pr P K Q prime U) :
    Pr P K Q prime U :=
  .seq (.seq (identitySeed d zero one seed tmp saved) generate) (bclear seed)

def seededSetupCost (d H cost : ℕ) : ℕ := d*(d*(6*H+6)+1)+1+cost+(2*(d*d*H)+2)

def SignedPassBound (regs : Fin 6 ↪ Fin T) (anchor : Fin (size d+T) ↪ Fin K)
    (ports : Fin (N+2) ↪ Fin K) (ext : Fin 6 ↪ Fin K) (v : Descriptor) (B : ℕ)
    (a : ScanData r d w W) (payload : ℕ → Record.Array d 1 (w+1) W)
    (rs : List (Pair (size d+T))) (parents saved : Fin (size d+T))
    (cs : List (Pair K)) (parentsC savedC : Fin K) (body : P → Pr P K Q prime U)
    (setup pass : Pr P K Q prime U) (setupCost : ℕ) (u : HS K Q prime U)
    (initial G : Stacks K prime) : Prop :=
    v.beforeH = B*prime^(r*((w+1)*r)) →
      a.records = LabelMask.records v → 0 < W →
      let D := embStk anchor G
      Ready d 1 (w+1) W D → ready (prime^w) D.R rs → D.R saved = [] →
      (D.R parents).length = v.beforeRows*v.rows*B →
      (D.R (port d regs 0)).length = ActualAffineScaling.modulus (w+1)^((d+1)*1)*W →
      a.signed = (List.range a.records).map payload →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port d regs i) = []) →
      ScanReady a ports ext 0 (preparedPivots a (ports (Fin.last N).castSucc)
        G) →
      M < 2^a.H → W < 2^a.J → a.outputTail = [] → G.R (ext 0) = [] →
      ready (prime^w) G.R cs → G.R savedC = [] → (G.R parentsC).length = v.beforeRows*v.rows*B →
      (∀ j < a.records, Record.scalarArray (payload j) = SparseRoleCircuit.encode ∘ a.input j) →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
      ∃ symbol, Record.scalarArray (payload j) = fun _ => symbol) →
      let ins := signedInputs a.table (w+1) a.records payload
    let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
    ∃ (z : HS K Q prime U) (F : Stacks K prime) (n : ℕ), z.user = u.user ∧ F.R (ext 2) = output ++ a.inputTail ∧ F.R (ext 5) = [] ∧
      F.R (ext 0) = [] ∧ F.R (ports (Fin.last N).castSucc) = a.pivotTail ∧
      F.R (ports (archivePorts 0 (columnBank 34))) = a.matrixTail ∧
      n ≤ setupCost + ((1+((v.beforeRows*v.rows*B)*(LabelTraversal.time (prime^w) (r*r) 1+5)+4 +
          ((ins.map (fun x => Record.cost d T 1 (w+1) W x.1 + 2)).sum + 2) +
          (2*(a.records*(ActualAffineScaling.modulus (w+1)^((d+1)*1)*W))+2))) + (2*((v.beforeRows*v.rows*B)*(LabelTraversal.time (prime^w) (r*r) 1+5)+4) + (1+(((List.range a.records).map fun j => a.recordTime U j + 4).sum + 2 + (2*(a.records*(M^(d+1)*W))+2))))) ∧
      Exec body (.seq setup pass) (mk u initial) n (mk z F)

structure SeededQueueReady (w H records : ℕ) (proj : Matrix (Fin r) (Fin r) ℚ)
    (α α' : Fin r → ZMod M) (initial S : Stacks K prime) (bank : Fin 18 ↪ Fin K)
    (recip : Fin 16 ↪ Fin K) (pool : Fin ((conjugationDepth r+1)*13) ↪ Fin K)
    (coeff : Fin r → Fin r → Fin 4 ↪ Fin K) (clock count mask seed tmp archive : Fin K)
    (ancestor : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4))) : Prop where
  seedBlank : initial.R seed = []
  tmpBlank : S.R tmp = []
  weightBank : S.R (recip 13) = [] ∧ ∀ i j, let s := coeff i j
      S.R (s 1) = binSyms H (α i).val ∧ S.R (s 2) = binSyms H (α' j).val
  ready :
      (∀ i : Fin 18, i ∈ [0,3,4,5,6,7,11,14,15] → S.R (bank i) = []) ∧ (S.R (bank 8)).length = H ∧
      S.R (bank 9) = binSyms H 0 ∧ S.R (bank 10) = [] ∧
       (S.R clock).length = w ∧ S.R count = [] ∧ S.R (recip 14) = [] ∧
      S.R (recip 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ S.R (recip 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (recip i) = []) ∧
      (∀ k ≤ conjugationDepth r, S.R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ conjugationDepth r, ∀ i : Fin 13, i ≠ 2 → S.R (frame pool k i) = []) ∧
      (∃ suffix, S.R (bank 16) = matrixWords prime H (IntegerMultBounds.Swap.Modular.reduce M proj) ++ suffix) ∧
      S.R (bank 17) = binSyms H (1 : ZMod (prime^(w+1))).val
  widths : ∀ j < records, (S.R (bank 12)).length = (ancestor j).length
  width : (S.R (bank 1)).length = w+1
  empty : S.R (archive) = []
  directory : S.R (bank 2) = (List.range records).flatMap (LabelDirectory.entry ancestor r (w+1)) ++ tail
  output : S.R (bank 13) = []
  bits : S.R mask = (List.range records).map fun j => bitSymbol (LabelStock.live r (w+1) 1 j)

omit [M8.Machine.Net] in
/-- Generate the directory scan's selector tape from the label counters. The
scan consumes the selectors, so its queue endpoint agrees with the endpoint
computed directly from the initial stacks. -/
theorem generateMaskAndQueue (body : P → Pr P K Q prime U) (rs : List (Pair K))
    (hk : rs.length = r*r) (mask parents saved : Fin K)
    (layout : (parents :: saved :: (slots rs ++ [mask])).Nodup) :
    ∃ writeMask, ∀ (v : Descriptor) (w B : ℕ), v.beforeH = B*prime^(r*((w+1)*r)) →
      ∀ (u : HS K Q prime U) (S : Stacks K prime), ready (prime^w) S.R rs →
      S.R saved = [] → (S.R parents).length = v.beforeRows*v.rows*B → S.R mask = [] →
      let bits := (List.range (LabelMask.records v)).map fun j => bitSymbol (LabelStock.live r (w+1) 1 j)
      let filled := {S with R := Function.update S.R mask bits}
      ∀ (queue : Pr P K Q prime U) (dir archive : Fin K) (tail words : List (Fin (prime+4))) (cost : ℕ),
      (∀ (y : HS K Q prime U), ∃ (z : HS K Q prime U) (n : ℕ), z.user = y.user ∧ n ≤ cost ∧
        Exec body queue (mk y filled) n (mk z (queueResult filled mask dir archive tail words))) →
      ∃ (z : HS K Q prime U) (n : ℕ), z.user = u.user ∧ n ≤ (v.beforeRows*v.rows*B)*(LabelTraversal.time (prime^w) (r*r) 1+5)+4+cost ∧
        Exec body (.seq writeMask queue) (mk u S) n (mk z (queueResult S mask dir archive tail words)) := by
  obtain ⟨writeMask,run⟩ := record_writes (body := body) r rs hk mask parents saved layout
  refine ⟨writeMask,?_⟩
  intro v w B shape u S radix free count blank bits filled queue dir archive tail words cost consume
  obtain ⟨y,t,hy,ht,emit⟩ := run v (w+1) B (by omega) shape u S ⟨radix,free,count⟩
  rw [blank,List.append_nil] at emit
  simp only [LabelMask.selectors,List.map_map,Function.comp_def] at emit
  change Exec body writeMask (mk u S) t (mk y filled) at emit
  obtain ⟨z,n,hz,hn,scan⟩ := consume y
  have endpoint : queueResult filled mask dir archive tail words = queueResult S mask dir archive tail words := by
    simp [queueResult,filled,Function.update_idem]
  rw [endpoint] at scan
  exact ⟨z,t+n,hz.trans hy,Nat.add_le_add ht hn,.seq emit scan⟩

theorem generatedSignedResidualPass (regs : Fin 6 ↪ Fin T) (anchor : Fin (size d+T) ↪ Fin K)
    (ports : Fin (N+2) ↪ Fin K) (ext : Fin 6 ↪ Fin K) (off : ∀ i k, ports i ≠ ext k)
    (banks : ∀ i k, anchor i ≠ ports k) (external : ∀ i k, k ≠ 2 → anchor i ≠ ext k)
    (shared : anchor (port d regs 1) = ext 2)
    (capacity : (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ Q)
    (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)) (proj : Matrix (Fin r) (Fin r) ℚ)
    (idempotent : proj*proj = proj) (admissible : IntegerMultBounds.Swap.Modular.Admissible prime proj)
    (α α' : Fin r → ZMod M) (inverse : ∀ i, α i * α' i = 1)
    (body : P → Pr P K Q prime U) (rs : List (Pair (size d+T))) (hk : rs.length = r*r)
    (parents saved : Fin (size d+T)) (layout : (parents :: saved :: (slots rs ++ [port d regs 4])).Nodup)
    (cap : columnCapacity ≤ Q) (cs : List (Pair K)) (sizeC : cs.length = r*r) (parentsC savedC : Fin K)
    (maskRegs : (parentsC :: savedC :: (slots cs ++ [ext 0])).Nodup)
    (pivotRegs : (parentsC :: savedC :: (slots cs ++ [ports (Fin.last N).castSucc])).Nodup)
    (separate : ∀ k ∈ parentsC :: savedC :: slots cs, ∀ i, anchor i ≠ k) :
    ∃ pass, ∀ (placement : Fin ((36+2*r+1+(conjugationDepth r+1)*13)+3) ↪ Fin K),
    let size := 36+2*r+1+(conjugationDepth r+1)*13
    let archiveSlot : Fin (size+3) := ⟨36+2*r, by dsimp [size]; omega⟩
    let registers := placement.trans (Equiv.swap (placement archiveSlot)
      (ports (archivePorts 0 (columnBank 34)))).toEmbedding
    let host := QueueLayout.block (n := size) 0 (by dsimp [size]; omega) registers
    let control := QueueLayout.block (n := 3) size (Nat.le_refl _) registers
    let mask := control 0
    let seed := control 1
    let tmp := control 2
    let bank := QueueLayout.block (n := 18) 0 (by omega) host
    let recip := QueueLayout.block (n := 16) 18 (by omega) host
    let counters := QueueLayout.block (n := 2) 34 (by omega) host
    let clock := counters 0
    let count := counters 1
    let pool := QueueLayout.block (n := (conjugationDepth r+1)*13) (36+2*r+1) (by omega) host
    let coeff := fun i j : Fin r => (coefficientSlots i j).trans host
    let archive := host ⟨36+2*r, by omega⟩
    have archiveOff : ∀ i, bank (QueueLayout.directoryWork i) ≠ archive := fun i h => by
      have eq := congrArg Fin.val (host.injective h)
      change 0 + i.val = 36+2*r at eq
      omega
    have coeffOff : ∀ i j k l, recip k ≠ coeff i j l := fun i j k l h => by
      have eq := congrArg Fin.val (host.injective h)
      change 18+k.val = (coefficientSlots (extra := (conjugationDepth r+1)*13) i j l).val at eq
      fin_cases l <;> simp [coefficientSlots, Matrix.cons_val] at eq <;> (try split_ifs at *) <;> omega
    ∀ (ancestor : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
      (v : Descriptor) (B : ℕ) (base : ScanData r d w W) (payload : ℕ → Record.Array d 1 (w+1) W)
      (u : HS K Q prime U) (initial : Stacks K prime),
    let padWord := matrixWords prime base.H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    let S := {initial with R := Function.update initial.R seed padWord}
    SeededQueueReady w base.H base.records proj α α' initial S bank recip pool coeff clock count
      mask seed tmp archive ancestor tail →
    let scan := QueueLayout.scanPorts (QueueLayout.directoryWork.trans bank) archive archiveOff
    let active := LabelStock.live r (w+1) 1
    let livePrice := liveRecordCost r (d+1) w base.H (S.R (bank 12)).length
      (Finset.univ.sup fun ij : Fin r × Fin r => RingFormula.time base.H (readTime base.H)
        (numerator (matrixInput false) (matrixInput true) ij.1 ij.2))
      (RingFormula.time base.H (readTime base.H) (determinant (matrixInput (m := r) false)))
    let generate : Pr P K Q prime U := seededQueueBody r d e bank recip clock count pool coeff coeffOff scan mask seed tmp
    let setupCost := (List.range base.records).countP active * (livePrice + 4*((d+1)*(d+1)*base.H)) +
        (List.range base.records).countP (fun j => !active j) * (10*((d+1)*(d+1)*base.H)+6) +
        base.records * (4*(S.R (bank 12)).length+4+(r*r*(4*(w+1)+4)+1)+6) + 4
    let a := base.physical e proj α α'
    let G := queueResult initial mask (scan 2) archive tail (a.matrices 0)
    SignedPassBound regs anchor ports ext v B a payload rs parents saved cs parentsC savedC body
      (withIdentitySeed (d+1) (bank 9) (bank 17) seed (bank 4) tmp generate) pass
      (seededSetupCost (d+1) base.H setupCost) u initial G := by
  obtain ⟨pass,run⟩ := physicalSignedResidualPass (w := w) (W := W) regs anchor ports ext off banks external shared
    capacity e proj idempotent admissible α α' inverse body rs hk parents saved layout cap cs sizeC
    parentsC savedC maskRegs pivotRegs separate
  refine ⟨pass,?_⟩
  intro placement size archiveSlot registers host control mask seed tmp bank recip counters clock count pool coeff archive archiveOff
    coeffOff ancestor tail v B base payload u initial padWord S queueInputs scan active livePrice generate setupCost a G shape records hW D
    neutral radix free count width unsigned clean start hm hw fresh maskEmpty radixC freeC countC encoded padding
  obtain ⟨seedBlank,tmpBlank,weightBank,queueReady,widths,width0,empty,directory,output,bits⟩ := queueInputs
  have blank := queueReady.1 4 (by decide)
  have sharedArchive : archive = ports (archivePorts 0 (columnBank 34)) := by
    change Equiv.swap (placement archiveSlot) _ (placement _) = _
    have slot : (⟨0+(36+2*r), by dsimp [size]; omega⟩ : Fin (size+3)) = archiveSlot :=
      Fin.ext (Nat.zero_add _)
    exact (congrArg (fun k => Equiv.swap (placement archiveSlot) _ (placement k)) slot).trans
      (Equiv.swap_apply_left ..)
  have apart (i j) : host i ≠ control j := QueueLayout.block_ne _ _ registers (by omega) i j
  have copyPorts (k : Fin 18) (hk : k ≠ 4) : [bank k,seed,bank 4,tmp].Nodup := by
    simp [seed,tmp,bank.injective.eq_iff,control.injective.eq_iff,hk,
      show bank k ≠ control 1 from apart _ _,show bank k ≠ control 2 from apart _ _,
      show control 1 ≠ bank 4 from (apart _ _).symm,show bank 4 ≠ control 2 from apart _ _]
  have bankKeep (k : Fin 18) : S.R (bank k) = initial.R (bank k) :=
    Function.update_of_ne (apart _ 1) _ _
  have tmpKeep : S.R tmp = initial.R tmp := Function.update_of_ne (control.injective.ne (by decide : (2 : Fin 3) ≠ 1)) _ _
  obtain ⟨prepared,steps,preparedUser,initCost,initRun⟩ := identitySeed_writes («M» := M) body
    (d+1) base.H (bank 9) (bank 17) seed (bank 4) tmp (copyPorts 9 (by decide))
    (copyPorts 17 (by decide)) u initial ⟨(bankKeep 9).symm.trans queueReady.2.2.1,
      (bankKeep 17).symm.trans (by obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,oneWord⟩ := queueReady; exact oneWord),
      (bankKeep 4).symm.trans blank,tmpKeep.symm.trans tmpBlank⟩
  rw [seedBlank,List.append_nil] at initRun
  have seedWord : S.R seed = padWord := Function.update_self ..
  obtain ⟨_,y,t,hy,ht,generateRun⟩ := physicalResidualQueue_exec body w base.records
    (IntegerMultBounds.Swap.Modular.reduce M proj) base.H hm registers ancestor tail e α α' prepared S
    seedWord tmpBlank weightBank queueReady widths width0 blank empty directory output bits
  let words := (List.range base.records).flatMap fun j => if active j then matrixWords prime base.H
    (projectorResidual e (IntegerMultBounds.Swap.Modular.reduce M proj) α α' (physicalLabel r (w+1) j)) else padWord
  change Exec body generate (mk prepared S) t (mk y (queueResult S mask (scan 2) archive tail words)) at generateRun
  have archiveEq : words = a.matrices 0 := (base.physical_archive e proj α α').symm
  rw [archiveEq] at generateRun
  obtain ⟨cleaned,cleanUser,clearRun⟩ := clearQueueSeed_exec body seed mask (scan 2) archive
    (control.injective.ne (by decide : (1 : Fin 3) ≠ 0)) (apart _ 1).symm (apart _ 1).symm
    padWord tail (a.matrices 0) y initial seedBlank
  have padLen : padWord.length = (d+1)*(d+1)*base.H := length_matrixWords ..
  have installed : G.R archive = a.matrices 0 := Function.update_self ..
  have prep : Function.update G.R archive (a.matrices 0) = G.R := by rw [← installed,Function.update_eq_self]
  obtain ⟨z,E,n,hz,queue,acc,maskDone,pivots,archiveDone,hn,exec⟩ :=
    run v B base payload cleaned G shape records hW neutral radix free count width unsigned clean
      (sharedArchive ▸ installed.trans (base.physical_archive e proj α α')) (by
        change ScanReady a ports ext 0 (preparedPivots a _ {G with R := Function.update G.R (ports (archivePorts 0 (columnBank 34))) (a.matrices 0)})
        rw [← sharedArchive,prep]
        exact start)
      hm hw fresh maskEmpty radixC freeC countC encoded padding
  exact ⟨z,E,_,hz.trans (cleanUser.trans (hy.trans preparedUser)),queue,acc,maskDone,pivots,archiveDone,Nat.add_le_add (Nat.add_le_add (Nat.add_le_add initCost ht) (Nat.le_of_eq (congrArg (fun n => 2*n+2) padLen))) hn,
    Exec.seq (Exec.seq (Exec.seq initRun generateRun) clearRun) exec⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
