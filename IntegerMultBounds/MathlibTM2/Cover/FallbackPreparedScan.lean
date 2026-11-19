module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignedHandoff
public import IntegerMultBounds.MathlibTM2.Cover.FallbackResidualPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackControlStreams
public import IntegerMultBounds.MathlibTM2.Cover.FallbackArchivedResidual

/-! Scan physical records with the prepared residual machine, reusing its exchange and parent tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz
open M8 ActualAffineScaling FlatCoordinateLayout LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- A fixed program signs and transforms every compatible queue, across precisions and payload widths. -/
theorem preparedPass_exec {Q T r A : ℕ} (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (capacity : columnCapacity ≤ Q) (signCapacity : (fieldSignProgram (0 : Fin (d+1)) true).1 ≤ Q) :
    let rows := List.finRange d
    let reads := pivotReads rows
    let n := reads.length
    let k := fun _ : Fin n => (0 : Fin (d+1))
    let j := fun a => (reads.get a).1
    let t := fun a => (j a).succ
    let i := fun a => (reads.get a).2
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let ports := Fin.castAddEmb (n := (N+1)+total) 1
    let shared := (Fin.castAddEmb (n := N+1) total).trans ports
    let bank := fun a => (exchangeBank (N+1) width a).trans ports
    let program : Fin n → Pr Empty (((N+1)+total)+1) Q prime U := fun a =>
      let host := Fin.castAddEmb (n := N+1) (width a)
      let sign := extendSignBank columnBank (fieldSignSlots (k a))
      statePlacedNormalized (bank a) (le_refl Q) (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
        (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange (j a).val (i a).val (k a) (t a)))
          (.seq (installFieldHeaders ((installerPorts _).trans sign))
            (placedFieldNeg (k a) ((signPorts _).trans sign) signCapacity)))
    let spare := Fin.last ((N+1)+total)
    let off : ∀ h, shared h ≠ spare := shared_ne_last (t := total)
    let reverseHost := rewindPorts (d+1) shared spare off
    let reverseBank := fun n => columnBank.trans (archivePorts n)
    let active := reverseBank (d+1)
    let pop : Pr Empty (N+2) columnCapacity prime U := .seq (dropWords (active 2) (active 34) (active 0) (d+1))
      (dropWords (active 2) (Fin.last N).castSucc (active 0) d)
    let rewind : Pr Empty (((N+1)+total)+1) Q prime U := statePlacedNormalized reverseHost capacity columnCapacity_pos Empty.elim
      (.seq pop (reverseStages (d+1) (d+1)))
    let residual := .seq ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done)) rewind
    let privateBank := (Fin.natAddEmb (m := total) (N+1)).trans ports
    ∀ (host : Fin (((N+1)+total)+1) ↪ Fin T) (ext : Fin 6 ↪ Fin T) (outside : ∀ i k, host i ≠ ext k)
      (parentTape : Fin T) (parentOff : ∀ i, host i ≠ parentTape) (parentExt : ∀ i, ext i ≠ parentTape)
      (body : P → Pr P T Q prime U),
      let scanPorts := reverseHost.trans host
      let tapes := (reverseBank 0).trans scanPorts
      let src := ext 2
      let acc := ext 5
      let pivot := scanPorts (Fin.last N).castSucc
      ∀ (rs : List (Pair T)) (_ : rs.length = r*r) (parents scratch : Fin T),
      (parents :: scratch :: (slots rs ++ [ext 0])).Nodup →
      (parents :: scratch :: (slots rs ++ [pivot])).Nodup →
      ∀ (regs : Fin 6 ↪ Fin A) (anchor : Fin (size d+A) ↪ Fin T)
        (ars : List (Pair (size d+A))) (ap asaved : Fin (size d+A)),
      (anchorProgram d true).1+(anchorProgram d false).1+1 ≤ Q → ars.length = r*r →
      (ap :: asaved :: (slots ars ++ [port d regs 4])).Nodup →
      (∀ i j, anchor i ≠ host j) → (∀ i k, k ≠ 2 → anchor i ≠ ext k) → anchor (port d regs 1) = src →
      (∀ i, anchor i ≠ parentTape) → (∀ k ∈ parents :: scratch :: slots rs, ∀ i, anchor i ≠ k) →
      ∃ prog : Pr P T Q prime U, ∀ {w W : ℕ} (a : ScanData r d w W) (parent : Fin d → (ZMod (prime^(w+1)))ˣ), a.table = table →
      ∀ (inputs : ℕ → Array d 1 (w+1) W),
      (∀ j < a.records, scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j) →
      a.signed = (List.range a.records).map inputs →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = true →
        ((a.matrix j).det = 1 ∨ (a.matrix j).det = -1) ∧
        (LabelRing.res prime (w+1) (by omega)).mapMatrix (a.matrix j) = a.table (LabelStock.residue r (w+1) 1 j)) →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
        ∃ symbol, scalarArray (inputs j) = fun _ => symbol) →
      (prime^(w+1)) < 2^a.H → W < 2^a.J → 0 < W →
      let H := a.H
      let J := a.J
      let cost := fun a =>
        let shear := fun neg => 1+cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
          (Function.Embedding.refl _) prime (j a).val (i a).val (k a) (t a) neg w W H J
        let swap := 1+completeSwapTime (P := Empty) (U := U) Empty.elim (d+1) (k a) (t a) w W H J
        1+(1+(2*shear false+shear true+2*swap)+((10*J+12)+(21*(w+1)+12)+1+
          (1+(AtomSegment.chainConst (fieldSignOps (k a) true)*((prime^(w+1))^(d+1)*W)*(width a+5)+6))))
      let stageCost := fun idx => 1+Finset.univ.sup (fun k => columnProgramTime U k (a.pivots idx k) w W H J)+((d+1)*(d+1)*(4*H+4)+1)
      let rewindCost := fun idx => 1+(((d+1)*(4*H+4)+1+(d*(4*H+4)+1))+((d+1)*stageCost idx+1))
      let bound := fun idx => ((List.finRange n).map cost).sum+1+rewindCost idx
      let cleanBound := fun idx => bound idx+(total*4+1+total*(6*(Fast.Main.mnProgPush residual*bound idx)))
      let volume := (prime^(w+1))^(d+1)*W
      let prepTime := (d+1)*(2*(d+1)+(4*w+4+columnTime (d+1) prime w H))+1 +
        (d*(8*((d+1)*(d+1)*H)+14*H+22)+1)+(6*H+6)+(4*((d+1)*H)+4)+(6*(d*H)+6)
      let stepTime := fun idx => (if LabelStock.live r (w+1) 1 idx then prepTime+((6*volume+6)+(1+cleanBound idx))
        else 4*(d+1)*(d+1)+1)+(4*volume+4)+((d+1)*(d+1)*(4*H+4)+1)
      ∀ (desc : RecursiveInterchangeLayout.Descriptor) (B : ℕ) (v : HS T Q prime U) (S : Stacks T prime),
      a.records = LabelMask.records desc → desc.beforeH = B*prime^(r*((w+1)*r)) →
      LabelTraversal.ready (prime^w) S.R rs → S.R scratch = [] → (S.R parents).length = desc.beforeRows*desc.rows*B →
      a.outputTail = [] → S.R (ext 0) = [] →
      let D := embStk anchor S
      Ready d 1 (w+1) W D → LabelTraversal.ready (prime^w) D.R ars → D.R asaved = [] →
      (D.R ap).length = desc.beforeRows*desc.rows*B →
      (D.R (port d regs 0)).length = ActualAffineScaling.modulus (w+1)^((d+1)*1)*W →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port d regs i) = []) →
      S.R src = ((List.range a.records).map inputs).flatMap payloadWord ++ a.inputTail →
      (S.R (ext 1)).length = volume → S.R (ext 3) = [] → S.R (ext 4) = [] → S.R acc = [] →
      S.R pivot = a.pivotTail → S.R (tapes 34) = a.matrices 0 →
      S.R (tapes 2) = binSyms H (prime^(w+1)) → S.R (tapes 27) = binSyms J W →
      S.R (tapes 28) = binSyms 1 1 → S.R (tapes 32) = binSyms H (1 : ZMod (prime^(w+1))).val →
      (S.R (tapes 33)).length = w →
      (∀ i ∈ shearWork, S.L (tapes i) = [] ∧ S.R (tapes i) = []) →
      (∀ i : Fin 35, i = 24 ∨ i = 25 → ∀ z, readAt blank (S.L (tapes i)) (S.R (tapes i)) z = blank) →
      (∀ i : Fin N, 35 ≤ i.val → S.L (scanPorts (columnPorts i).castSucc) = [] ∧ S.R (scanPorts (columnPorts i).castSucc) = []) →
      S.R parentTape = (List.ofFn fun j => binSyms H (parent j : ZMod (prime^(w+1))).val).flatten →
      (∀ i, S.L (host (privateBank i)) = [] ∧ S.R (host (privateBank i)) = []) →
      let output := (List.range a.records).flatMap (outputRecord (LabelStock.live r (w+1) 1) a.matrix a.input)
      ∃ z F l, z.user = v.user ∧ F.R src = output ++ a.inputTail ∧ F.R acc = [] ∧ F.R (ext 0) = [] ∧
        F.R (scanPorts (Fin.last N).castSucc) = a.pivotTail ∧ F.R (tapes 34) = a.matrixTail ∧
        F.R parentTape = S.R parentTape ∧ (∀ h, F.L (host (privateBank h)) = [] ∧ F.R (host (privateBank h)) = []) ∧
        l ≤ (1+((desc.beforeRows*desc.rows*B)*(time (prime^w) (r*r) 1+5)+4 +
          (((signedInputs a.table (w+1) a.records inputs).map (fun x => Record.cost d A 1 (w+1) W x.1 + 2)).sum + 2) +
          (2*(a.records*(ActualAffineScaling.modulus (w+1)^((d+1)*1)*W))+2))) + 2*((desc.beforeRows*desc.rows*B)*(time (prime^w) (r*r) 1+5)+4) + (((List.range a.records).map fun idx => stepTime idx+4).sum+2+(2*(a.records*volume)+2)) ∧
        Exec body prog (mk v S) l (mk z F) := by
  intro rows reads n k j t i width total ports shared bank program spare off reverseHost reverseBank active pop rewind residual privateBank host ext outside parentTape parentOff parentExt body scanPorts tapes src acc pivot rs sizeRs parents scratch maskRegs pivotRegs regs anchor ars ap asaved acap asize alayout banks external sharedSrc anchorParent counters
  let positive := lt_of_lt_of_le columnCapacity_pos capacity
  let cols := shared.trans host
  let prep := forwardBank.trans (rewindPorts (d+1) cols (host spare) (fun i => host.injective.ne (off i)))
  let stream := cols (Fin.last N)
  let count := ext 1
  let saved := ext 3
  let tmp := ext 4
  let dst := cols (columnBank 24)
  let prepare : Pr P T Q prime U := Prog.seq (.seq (.seq (recordWeights d prep stream) (copyWordHeader (prep 20) (prep 14) (prep 3) (prep 4)))
      (moveRightOrdered (prep 14) (prep 3) (stageBank prep (d+1) 15))) (copyWordHeader parentTape stream (prep 3) (prep 4))
  let compute : Pr P T Q prime U := Prog.seq (movePrefix count src dst saved tmp) (statePlacedNormalized host le_rfl positive Empty.elim
    (.seq residual (clearWorkTapes ((List.finRange total).map privateBank))))
  let advance : Pr P T Q prime U := dropWords (tapes 2) (tapes 34) (tapes 0) ((d+1)*(d+1))
  let live : Pr P T Q prime U := Prog.seq (.seq (.seq prepare compute) (Mult.ShortConv.transfer count (tapes 24) acc tmp)) advance
  let pad : Pr P T Q prime U := Prog.seq (paddingRecord (d+1) (scanPorts (Fin.last N).castSucc) count src acc tmp) advance
  have offExt (i : Fin (N+2)) (k : Fin 6) : scanPorts i ≠ ext k := outside _ _
  have streamEq : scanPorts (Fin.last N).castSucc = stream := by
    have eq := DFunLike.congr_fun (rewindPorts_active (d+1) shared spare off) (Fin.last N)
    exact congrArg host (by simpa only [Function.Embedding.trans_apply,archivePorts_stream] using eq)
  have prepOff (i : Fin 23) : prep i ≠ parentTape := by
    have eq := DFunLike.congr_fun (rewindPorts_trans (d+1) shared spare off host) (forwardBank i)
    exact eq ▸ parentOff _
  obtain ⟨writer,emit⟩ := controlStreams_exec body table rs sizeRs (ext 0) pivot parents scratch maskRegs pivotRegs
  obtain ⟨sign,signRun⟩ := anchorHandoff regs anchor scanPorts ext offExt
    (fun i j => banks i _) external sharedSrc acap table body ars asize ap asaved alayout
  refine ⟨.seq (.seq sign writer) (.seq (maskedScan (ext 0) live pad) (moveR acc src id)),?_⟩
  intro w W a parent tables inputs encoded unsigned liveSpec padding hm hw hW H J cost stageCost rewindCost bound cleanBound volume prepTime stepTime
  subst table
  intro desc B first init records shape radixInit scratchInit countInit fresh emptyInit anchorView neutral aradix afree acount awidth clean queueInit extCount savedEmpty tmpEmpty accEmpty pivotTail archive modWord widthWord one padded ticks scratchFree payloadBlank sharedFree parentWord privateFree output

  let invariant := fun outs idx (D : Stacks T prime) => ScanReady {a with signed := outs} scanPorts ext idx D ∧
    D.R parentTape = (List.ofFn fun j => binSyms H (parent j : ZMod (prime^(w+1))).val).flatten ∧
    ∀ h, D.L (host (privateBank h)) = [] ∧ D.R (host (privateBank h)) = []
  let installed := preparedPivots a pivot init
  have laneOff (i : Fin 35) : tapes i ≠ pivot := by
    apply scanPorts.injective.ne
    rw [← archivePorts_stream 0]
    apply (archivePorts 0).injective.ne
    intro eq
    have e := congrArg Fin.val eq
    change i.val = N at e
    omega
  have laneR (i : Fin 35) : installed.R (tapes i) = init.R (tapes i) := Function.update_of_ne (laneOff i) _ _
  have extR (i : Fin 6) : installed.R (ext i) = init.R (ext i) := Function.update_of_ne (offExt _ i).symm _ _
  have initialInv : invariant a.signed 0 installed := by
    refine ⟨⟨?_,(congrArg List.length (extR 1)).trans extCount,(extR 3).trans savedEmpty,(extR 4).trans tmpEmpty,
      ?_,?_,(laneR 34).trans archive,?_,?_,?_⟩,(Function.update_of_ne (parentOff _).symm _ _).trans parentWord,?_⟩
    · simpa only [List.drop_zero,unsigned] using (extR 2).trans queueInit
    · simpa [outputPrefix,fresh] using (extR 5).trans accEmpty
    · change installed.R pivot = _
      rw [show installed.R pivot = (List.range a.records).flatMap a.pivotWord ++ init.R pivot from Function.update_self ..,
        pivotTail,List.drop_zero]
    · intro i hi
      have ne : scanPorts (columnPorts i).castSucc ≠ pivot := scanPorts.injective.ne (fun eq => i.isLt.ne (congrArg Fin.val eq))
      exact ⟨(sharedFree i hi).1,(Function.update_of_ne ne _ _).trans (sharedFree i hi).2⟩
    · intro z
      change readAt blank (init.L (tapes 24)) (installed.R (tapes 24)) z = blank
      rw [laneR]; exact payloadBlank 24 (Or.inl rfl) z
    · intro inside
      refine ⟨(laneR 2).trans modWord,(laneR 27).trans widthWord,(laneR 28).trans one,(laneR 32).trans padded,
        (congrArg List.length (laneR 33)).trans ticks,((laneR 34).trans archive).trans (a.matrices_succ inside),
        fun i hi => ⟨(scratchFree i hi).1,(laneR i).trans (scratchFree i hi).2⟩,?_,?_⟩
      · intro z
        change readAt blank (init.L (tapes 24)) (installed.R (tapes 24)) (z-0) = _
        rw [laneR,sub_zero,payloadBlank 24 (Or.inl rfl)]
        simp only [Function.comp_def,List.ofFn_const,putWord_blanks]
        rfl
      · intro z
        change readAt blank (init.L (tapes 25)) (installed.R (tapes 25)) (z-0) = _
        rw [laneR,sub_zero,payloadBlank 25 (Or.inr rfl)]
        rfl
    · intro i
      have ne := host.injective.ne (private_ne_rewind (d+1) i (Fin.last N).castSucc)
      exact ⟨(privateFree i).1,(Function.update_of_ne ne _ _).trans (privateFree i).2⟩
  obtain ⟨outs,initial,base,signTime,signed,signUser,signExec,scanStart,signFrame,signBound⟩ :=
    signRun desc B a inputs first init shape records hW neutral aradix afree acount awidth unsigned clean initialInv.1
  let scanData := {a with signed := outs}
  let ready := invariant outs
  have scratchEmpty := (signFrame scratch (counters scratch (by simp))).2.trans scratchInit
  have countLen := (congrArg List.length (signFrame parents (counters parents (by simp))).2).trans countInit
  have maskEmpty := (signFrame _ (fun i => external i 0 (by decide))).2.trans emptyInit
  have radix : LabelTraversal.ready (prime^w) base.R rs := by
    intro pair hp
    have eq (k) (hk : k ∈ slots rs) := (signFrame k (counters k (by simp [hk]))).2
    rw [eq _ (List.mem_flatMap.mpr ⟨pair,hp,by simp⟩),eq _ (List.mem_flatMap.mpr ⟨pair,hp,by simp⟩)]
    exact radixInit pair hp
  have initialReady : ready 0 (preparedPivots scanData pivot base) := by
    refine ⟨scanStart,?_,?_⟩
    · exact ((Function.update_of_ne (parentOff _).symm _ _).trans (signFrame _ anchorParent).2).trans
        ((Function.update_of_ne (parentOff _).symm _ _).symm.trans initialInv.2.1)
    · intro h
      have separate := host.injective.ne (private_ne_rewind (d+1) h (Fin.last N).castSucc)
      have kept := signFrame _ (fun i => banks i (privateBank h))
      exact ⟨kept.1.trans (initialInv.2.2 h).1,((Function.update_of_ne separate _ _).trans kept.2).trans
        ((Function.update_of_ne separate _ _).symm.trans (initialInv.2.2 h).2)⟩
  obtain ⟨v,t,hv,ht,write⟩ := emit desc (w+1) B (by omega) shape initial base (by simpa using radix) scratchEmpty countLen
  let bits := (LabelMask.selectors r (w+1) a.records).map (bitSymbol (a := prime))
  let prepared := {base with R := Function.update base.R pivot ((List.range a.records).flatMap a.pivotWord ++ base.R pivot)}
  let S := {prepared with R := Function.update prepared.R (ext 0) bits}
  have gen : Exec body writer (mk initial base) t (mk v S) := by
    have code : a.pivotWord = fun j => scheduleCode (a.pivots j) ++ orderedScheduleCode (List.finRange (d+1)).reverse (a.pivots j) := rfl
    simpa [S,prepared,bits,pivot,← records,code,ScanData.pivotWord,ScanData.pivots,maskEmpty,offExt,
      Function.update_comm (offExt (Fin.last N).castSucc 0)] using write
  have start : ready 0 S := ⟨initialReady.1.mask (fun i => offExt i 0) bits,
    (Function.update_of_ne (parentExt 0).symm _ _).trans initialReady.2.1,
    fun h => ⟨(initialReady.2.2 h).1,(Function.update_of_ne (outside _ 0) _ _).trans (initialReady.2.2 h).2⟩⟩
  have mask : S.R (ext 0) = bits := Function.update_self ..
  have scanned : ∃ z F l, z.user = v.user ∧ ready a.records F ∧ F.R (ext 0) = [] ∧
        l ≤ ((List.range a.records).map fun idx => stepTime idx+4).sum+2 ∧
        Exec body (maskedScan (ext 0) live pad) (mk v S) l (mk z F) := by
    apply maskedRange_exec body (ext 0) live pad a.records (LabelStock.live r (w+1) 1) stepTime ready ?_ ?_ v S start
      (by simpa [bits,LabelMask.selectors,List.map_map,Function.comp_def] using mask)
    · intro idx D bits h
      exact ⟨h.1.mask (fun i => offExt i 0) bits,(Function.update_of_ne (parentExt 0).symm _ _).trans h.2.1,
        fun i => ⟨(h.2.2 i).1,(Function.update_of_ne (outside _ 0) _ _).trans (h.2.2 i).2⟩⟩
    intro idx inside u D current
    obtain ⟨before,parents,free⟩ := current
    cases bit : LabelStock.live r (w+1) 1 idx with
    | false =>
      obtain ⟨symbol,constant⟩ := padding idx inside bit
      obtain ⟨z,F,l,hz,next,left,frame,hn,run⟩ := before.padding scanData scanPorts ext offExt idx inside bit inputs
        (encoded idx inside) symbol constant signed body u D
      refine ⟨z,F,l,hz,⟨next,(frame _ (parentExt 2).symm (parentExt 5).symm (fun i => parentOff _)).trans parents,?_⟩,
        frame _ (ext.injective.ne (by decide)) (ext.injective.ne (by decide)) (fun i => offExt i 0),
        by simpa only [stepTime,bit,Bool.false_eq_true,ite_false] using hn,by simpa only [bit,Bool.false_eq_true,ite_false] using run⟩
      intro h
      exact ⟨(congrFun left _).trans (free h).1,(frame _ (outside _ 2) (outside _ 5)
        (fun i => host.injective.ne (private_ne_rewind (d+1) h i).symm)).trans (free h).2⟩
    | true =>
      obtain ⟨det,lift⟩ := liveSpec idx inside bit
      have addr := physicalLabel_index (m := r) (w := w+1) idx
      have res := physicalLabel_residue (m := r) (w := w+1) (by omega) idx
      have step := preparedResidual_exec parent capacity signCapacity H J hm hw hW a.table (physicalLabel r (w+1) idx)
        (a.matrix idx) det (lift.trans (congrArg a.table res)) _ (addr.symm ▸ inside) inputs outs signed
        (a.matrices (idx+1)) a.pivotTail (fun _ => blank) 0 (by simp) (a.input idx) host body u D
        count src saved tmp (fun i => outside i 2) a.inputTail parentTape prepOff (parentOff _).symm parents
        (by obtain h := before.bank inside; exact ⟨h.modulus,h.width,h.one,h.padded,h.clock,h.archive,h.scratch,h.src,h.dst⟩)
        (by rw [addr]; exact (congrArg D.R streamEq.symm).trans before.pivots)
      simp only [addr,← res] at step
      have sep (i k : Fin 6) (h : i ≠ k) := ext.injective.ne h
      obtain ⟨z,F,l,word,hz,hn,run,effect,out,blanked,archive,next,reset,clean,pivots,_,queue,frame⟩ :=
        step acc (fun i => outside i 1) (fun i => outside i 4) (fun i => outside i 5) (sep 5 2 (by decide))
          (by simp [count,acc,tmp,ext.injective.eq_iff,outside,Ne.symm (outside _ _)])
          ⟨(outside _ 3).symm,(outside _ 3).symm,(outside _ 3).symm⟩
          (by simp [count,src,saved,tmp,ext.injective.eq_iff,outside,Ne.symm (outside _ _)])
          before.count before.saved before.tmp (encoded idx inside) before.queue before.free free
      have same (h : Fin 6) (hs : h ≠ 2) (ha : h ≠ 5) := (frame (ext h) (sep _ _ hs) (sep _ _ ha) (fun i => outside i h)).2
      have unit : IsUnit (a.matrix idx).det := by rcases det with h | h <;> simp [h]
      refine ⟨z,F,l,hz,⟨⟨queue,(congrArg List.length (same 1 (by decide) (by decide))).trans before.count,
        (same 3 (by decide) (by decide)).trans before.saved,(same 4 (by decide) (by decide)).trans before.tmp,
        ?_,pivots,archive,clean,blanked,fun hj => by
          obtain h := next _ _ (a.input (idx+1)) (a.matrices_succ hj)
          exact ⟨h.modulus,h.width,h.one,h.padded,h.clock,h.archive,h.scratch,h.src,h.dst⟩⟩,
        (frame parentTape (parentExt 2).symm (parentExt 5).symm parentOff).2.trans parents,reset⟩,
        same 0 (by decide) (by decide),by simp only [stepTime,bit,ite_true]; exact hn,
        by simp only [ite_true]; exact run⟩
      rw [outputPrefix_succ,outputRecord_live _ _ _ bit unit word effect,← before.acc]
      exact out
  obtain ⟨u,D,l,hu,⟨done,parents,free⟩,empty,time,run⟩ := scanned
  obtain ⟨z,F,hz,queue,accEnd,maskEnd,pivots,archive,frame,move⟩ := finishScan_exec scanData scanPorts ext offExt body
    u D done fresh (by simpa [signedInputs] using signed.length_eq.symm) empty
  refine ⟨z,F,_,hz.trans (hu.trans (hv.trans signUser)),queue,accEnd,maskEnd,pivots,archive,
    (frame _ (parentExt 2).symm (parentExt 5).symm).2.trans (parents.trans (initialReady.2.1.symm.trans ((Function.update_of_ne (parentOff _).symm _ _).trans (signFrame _ anchorParent).2))),?_,
    Nat.add_le_add (Nat.add_le_add signBound (by simpa using ht)) (Nat.add_le_add_right time _),Exec.seq (Exec.seq signExec gen) (Exec.seq run move)⟩
  intro h
  have keep := frame _ (outside (privateBank h) 2) (outside (privateBank h) 5)
  exact ⟨keep.1.trans (free h).1,keep.2.trans (free h).2⟩


end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
