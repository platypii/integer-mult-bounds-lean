module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackGeneratedSignedPass
public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignedHandoff
public import IntegerMultBounds.MathlibTM2.Cover.FallbackResidualPass
public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectorySetup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackControlStreams
public import IntegerMultBounds.MathlibTM2.Cover.FallbackArchivedResidual

/-! Generate the physical residual archive and run the signed pass on the same tape bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz
open M8 ActualAffineScaling FlatCoordinateLayout LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

open RingFormula Node

def installMask {T : ℕ} (S : Stacks T prime) (mask : Fin T) (bits : List (Fin (prime+4))) : Stacks T prime :=
  {S with R := Function.update S.R mask bits}

omit [M8.Machine.Net] in
theorem reciprocal_ne_coefficient {r extra : ℕ} (i j : Fin r) (k : Fin 16) (l : Fin 4) :
    18+k.val ≠ (coefficientSlots (extra := extra) i j l).val := by
  fin_cases l <;> simp [coefficientSlots, Matrix.cons_val] <;> (try split_ifs) <;> omega

omit [M8.Machine.Net] in
theorem seedCopyPorts {T : ℕ} (bank : Fin 18 ↪ Fin T) (control : Fin 3 ↪ Fin T)
    (apart : ∀ i j, bank i ≠ control j) (k : Fin 18) (hk : k ≠ 4) :
    [bank k,control 1,bank 4,control 2].Nodup := by
  simp [bank.injective.eq_iff,control.injective.eq_iff,hk,apart,(apart 4 1).symm]

omit [M8.Machine.Net] in
theorem unitCopy_exec {T Q A : ℕ} (body : P → Pr P T Q A U) (bank : Fin 18 ↪ Fin T)
    (src tmp : Fin T) (srcOff : ∀ i, src ≠ bank i) (tmpOff : ∀ i, bank i ≠ tmp) (apart : src ≠ tmp)
    (v : HS T Q A U) (S : Stacks T A) (word : List (Fin (A+4))) (source : S.R src = word)
    (dest : S.R (bank 17) = []) (work : S.R (bank 4) = []) (saved : S.R tmp = []) :
    ∃ u, u.user = v.user ∧ Exec body (bcopy src (bank 17) (bank 4) tmp) (mk v S) (6*word.length+6)
      (mk u {S with R := Function.update S.R (bank 17) word}) := by
  obtain ⟨u,hu,run⟩ := bcopy_exec body (a := src) (c := bank 17) (t₁ := bank 4) (t₂ := tmp)
    (by simp [srcOff,tmpOff,apart]) v S work saved
  exact ⟨u,hu,by simpa only [source,dest,List.append_nil] using run⟩

noncomputable def exchangeTime (U : Type) {m : ℕ} (j i : ℕ) (k t : Fin m)
    (width w W H J : ℕ) : ℕ :=
  let shear := fun neg => 1+cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
    (Function.Embedding.refl _) prime j i k t neg w W H J
  let swap := 1+completeSwapTime (P := Empty) (U := U) Empty.elim m k t w W H J
  1+(1+(2*shear false+shear true+2*swap)+((10*J+12)+(21*(w+1)+12)+1+
    (1+(AtomSegment.chainConst (fieldSignOps k true)*((prime^(w+1))^m*W)*(width+5)+6))))

theorem exchangeTime_le_setup_add_width_volume (U : Type) {m : ℕ} (j i : ℕ)
    (k t : Fin m) (width : ℕ) :
    ∃ swaps shears : ℕ, ∀ w W H J, exchangeTime U j i k t width w W H J ≤
      exchangeTime U j i k t width w 0 H J +
        (swaps*swapVolumeRate w+shears)*((prime^(w+1))^m*W) := by
  let shear := fun neg w W H J => cleanChildShearTime (P := Empty) (U := U) (A := prime)
    Empty.elim (Function.Embedding.refl _) prime j i k t neg w W H J
  have shearRate (neg : Bool) : ∃ c : ℕ, ∀ w W H J, shear neg w W H J =
      shear neg w 0 H J + c*((prime^(w+1))^m*W) :=
    ⟨_,fun w W H J => cleanChildShearTime_eq_setup_add_volume _ _ prime j i k t neg w W H J⟩
  let swap := fun w W H J => completeSwapTime (P := Empty) (U := U) Empty.elim m k t w W H J
  have swapRate : ∃ c : ℕ, ∀ w W H J, swap w W H J ≤
      swap w 0 H J + c*swapVolumeRate w*((prime^(w+1))^m*W) :=
    ⟨_,fun w W H J => completeSwapTime_le_setup_add_volume _ m k t w W H J⟩
  choose c hc using shearRate
  obtain ⟨s,hs⟩ := swapRate
  refine ⟨2*s,2*c false+c true+AtomSegment.chainConst (fieldSignOps k true)*(width+5),?_⟩
  intro w W H J
  unfold exchangeTime
  change 1+(1+(2*(1+shear false w W H J)+(1+shear true w W H J)+2*(1+swap w W H J))+
    ((10*J+12)+(21*(w+1)+12)+1+(1+(AtomSegment.chainConst (fieldSignOps k true)*((prime^(w+1))^m*W)*(width+5)+6)))) ≤ _
  rw [hc false w W H J,hc true w W H J]
  grw [hs w W H J]
  simp only [Nat.mul_zero,Nat.zero_mul]
  exact le_of_eq (by ring)

/-- A fixed program signs and transforms every compatible queue, across precisions and payload widths. -/
theorem archivedPass_exec {Q T r A : ℕ} (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
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
      let cost := fun a => exchangeTime U (j a).val (i a).val (k a) (t a) (width a) w W H J
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
        l ≤ (1+((desc.beforeRows*desc.rows*B)*(LabelTraversal.time (prime^w) (r*r) 1+5)+4 +
          (((signedInputs a.table (w+1) a.records inputs).map (fun x => Record.cost d A 1 (w+1) W x.1 + 2)).sum + 2) +
          (2*(a.records*(ActualAffineScaling.modulus (w+1)^((d+1)*1)*W))+2))) + 2*((desc.beforeRows*desc.rows*B)*(LabelTraversal.time (prime^w) (r*r) 1+5)+4) + (((List.range a.records).map fun idx => stepTime idx+4).sum+2+(2*(a.records*volume)+2)) ∧
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


omit [M8.Machine.Net] in
/-- Count both branches of a residual scan using the invertible labels in one box. -/
theorem residualBranchCounts (r w parents records : ℕ) (rows : records = parents*((prime^(w+1))^(r*r))) :
    let live := LabelStock.live r (w+1) 1
    let count := parents*((∏ i : Fin r, (prime^r-prime^i.val))*(prime^w)^(r*r))
    (List.range records).countP live = count ∧
      (List.range records).countP (fun j => !live j) = records-count := by
  intro live count
  have oneBox := (liveLabelCount (m := r) (by omega : 0 < w+1)).trans (LabelPadding.unit_count w)
  rw [liveClasses_eq_product] at oneBox
  have selected : (List.range records).countP live = count := by
    rw [rows]
    exact (LabelStock.count_boxes r (w+1) parents id).trans (congrArg (parents*·) oneBox)
  have partition := List.length_eq_countP_add_countP live (l := List.range records)
  simp only [List.length_range,decide_not,Bool.decide_eq_true,selected] at partition
  exact ⟨selected,by omega⟩

omit [M8.Machine.Net] in
/-- Charge the directory, radix traversal and generated archive to the supplier's preparation budget. -/
theorem residualPreparation_le (v : RecursiveInterchangeLayout.Descriptor) (r d w B width H : ℕ)
    (rankPos : 0 < r) :
    let parents := v.beforeRows*v.rows*B
    let box := (prime^(w+1))^(r*r)
    let records := LabelMask.records v
    let digits := (w+1)*(r*r)
    let units := ∏ i : Fin r, (prime^r-prime^i.val)
    let lifts := (prime^w)^(r*r)
    let live := parents*(units*lifts)
    let dirTime := 8*(w+1)+8+22*box + (parents*(6*box+10)+6 + (parents*box*(9*digits+15)+6 +
      (parents*(box*(8*width+11)+6*width+15)+6 + parents*box*(6*(width+digits)+13)+6)))
    let archiveTime := live*(matrixBuildCost r d w H + 12*r*r*width + 4*(d*d*H)) +
      (records-live)*(10*(d*d*H)+6) + records*(4*width+4+(r*r*(4*(w+1)+4)+1)+6)+4
    records = parents*box →
    (44*records+13*(w+1)+14 + dirTime + (26*prime^w+6)) +
      (parents*(LabelTraversal.time (prime^w) (r*r) 1+5)+4 + (archiveTime + paddingSetupCost d H)) ≤
      passPreparationCost v r d w B width H := by
  intro parents box records digits units lifts live dirTime archiveTime rowCount
  have boxSize : box = prime^(r*r)*lifts := by dsimp only [box,lifts]; rw [pow_succ',mul_pow]
  have hLive : live ≤ records := by
    dsimp only [live,units,lifts]
    rw [← (residualBranchCounts r w parents records rowCount).1]
    exact (List.countP_le_length).trans_eq (List.length_range)
  have archive := queueArchive_le records live (d*d*H) (matrixBuildCost r d w H) hLive
  have build := Nat.mul_le_mul_left live (matrixBuildCost_le r d w H)
  have traversal := LabelTraversal.time_add_ten_le (pow_pos prime_prime.pos w) (r*r) 1
  have traverse : LabelTraversal.time (prime^w) (r*r) 1+5 ≤ 11*box := by
    dsimp only [box]; rw [pow_succ]; omega
  have fixed := fixedBoxCost_le r w rankPos
  change 22*box + 21*(w+1) + 26*prime^w + 82 ≤ 151*box at fixed
  change _ ≤ parents*(lifts*(units*(matrixBuildCost r d 1 1*(w+1)*(H+1)^2) +
    prime^(r*r)*(10*(d*d*H)+6))) + directorySetupCost r (w+1) width parents records live box + paddingSetupCost d H
  have queueBill : parents*(lifts*(units*(matrixBuildCost r d 1 1*(w+1)*(H+1)^2) +
      prime^(r*r)*(10*(d*d*H)+6))) = live*(matrixBuildCost r d 1 1*(w+1)*(H+1)^2) + records*(10*(d*d*H)+6) := by
    rw [rowCount,boxSize]; unfold live; ring
  rw [queueBill]
  grw [traverse]
  dsimp only [dirTime,digits,archiveTime,directorySetupCost,inheritedLabelCost]
  rw [rowCount] at archive ⊢
  nlinarith only [archive,build,fixed,Nat.zero_le (parents*box)]

omit [M8.Machine.Net] in
theorem residualClassSum_le {α : Type} (accept : α → Bool) (cost : α → ℕ) (live pad : ℕ)
    (bound : ∀ x, cost x ≤ if accept x then live else pad) (xs : List α) :
    (xs.map cost).sum ≤ xs.countP accept*live + xs.countP (fun x => !accept x)*pad := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := bound x
    cases h : accept x <;> simp [h,Nat.add_mul] at hx ⊢ <;> omega

-- The earlier constant-pivot bound is preserved in d993aa31.
omit [M8.Machine.Net] in
theorem signedClassTime (count traversal copies volume : ℕ) (classes : List α) (anchor scan : α → ℕ) :
    (1+(count*traversal+4 + (copies*(classes.map anchor).sum+2) + (2*volume+2))) +
      2*(count*traversal+4) + (copies*(classes.map scan).sum+2+(2*volume+2)) =
    3*count*traversal + copies*(classes.map fun x => anchor x + scan x).sum + 4*volume+21 := by
  have addClasses : (classes.map fun x => anchor x + scan x).sum = (classes.map anchor).sum + (classes.map scan).sum := by rw [List.sum_map_add]
  rw [addClasses]
  ring

omit [M8.Machine.Net] in
theorem uniformResidualClassBound {r w W A H : ℕ}
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (cleanBound : (Fin (d+1) → Fin (d+1)) → ℕ) (kernel volume prepTime : ℕ)
    (kernelBound : ∀ p, cleanBound p ≤ kernel) :
    let classes := LabelSelectors.classes 1 (r*r)
    let anchorCost := anchorClassCost table A w W
    let stepTime := fun (m : Matrix (Fin r) (Fin r) (ZMod prime)) =>
      (if decide (m.det ≠ 0) then prepTime+((6*volume+6)+(1+cleanBound (classPivots (table m))))
       else 4*(d+1)*(d+1)+1)+(4*volume+4)+((d+1)*(d+1)*(4*H+4)+1)
    let scanCost := fun x => stepTime (LabelSelectors.matrix r x)+4
    let units := ∏ i : Fin r, (prime^r-prime^i.val)
    let anchorMax := max (Record.cost d A 1 (w+1) W false) (Record.cost d A 1 (w+1) W true) + 2
    let common := anchorMax + (4*volume+4) + ((d+1)*(d+1)*(4*H+4)+1) + 4
    let live := prepTime + ((6*volume+6)+(1+kernel))
    let pad := 4*(d+1)*(d+1)+1
    (classes.map fun x => anchorCost x + scanCost x).sum ≤ units*(common+live) + (prime^(r*r)-units)*(common+pad) := by
  intro classes anchorCost stepTime scanCost units anchorMax common live pad
  have classBound := residualClassSum_le (LabelSelectors.accept r) (fun x => anchorCost x + scanCost x)
    (common+live) (common+pad) (fun x => by
      let m := LabelSelectors.matrix r x
      have anchorLe : anchorCost x ≤ anchorMax := by
        dsimp only [anchorCost,anchorClassCost,anchorMax]
        change Record.cost d A 1 (w+1) W (negativeAnchor (classPivots (table m)) (table m)) + 2 ≤ _
        cases negativeAnchor (classPivots (table m)) (table m) <;> omega
      have kernelLe := kernelBound (classPivots (table m))
      change anchorCost x + (stepTime m+4) ≤ if decide (m.det ≠ 0) then common+live else common+pad
      by_cases h : m.det = 0 <;> simp only [stepTime,h,ne_eq,not_true_eq_false,decide_false,
        Bool.false_eq_true,ite_false,decide_eq_true_eq,not_false_eq_true,ite_true,common,live,pad] <;> omega) classes
  have selected : classes.countP (LabelSelectors.accept r) = units := invertibleClassCount r
  have sizeClasses : classes.length = prime^(r*r) := by simp [classes,LabelSelectors.classes_eq]
  have partition := List.length_eq_countP_add_countP (LabelSelectors.accept r) (l := classes)
  simp only [sizeClasses,selected,decide_not,Bool.decide_eq_true] at partition
  have other : classes.countP (fun x => !LabelSelectors.accept r x) = prime^(r*r)-units := by omega
  simpa only [selected,other] using classBound

omit [M8.Machine.Net] in
/-- Count the shared work once per record and the live payload moves only on invertible records. -/
theorem physicalPayloadBill (r copies volume common live pad rate records : ℕ)
    (rankPos : 0 < r) (rowCount : records = copies*prime^(r*r)) :
    let units := ∏ i : Fin r, (prime^r-prime^i.val)
    let active := copies*units
    let totalVolume := records*volume
    copies*(units*((common+4*volume)+(live+rate*volume)) + (prime^(r*r)-units)*((common+4*volume)+pad)) + 4*totalVolume =
      records*common + active*live + (records-active)*pad + 8*totalVolume +
        rate*min (active*volume) (((prime-1)*totalVolume)/prime) := by
  intro units active totalVolume
  have unitsLe : units ≤ prime^(r*r) := by
    calc
      _ ≤ ∏ _ : Fin r, prime^r := Finset.prod_le_prod fun i _ => Nat.sub_le _ _
      _ = _ := by simp [← pow_mul]
  have density := liveClassVolume_le r (copies*volume) rankPos
  rw [liveClasses_eq_product] at density
  have payload : active*volume ≤ ((prime-1)*totalVolume)/prime := by
    apply (Nat.le_div_iff_mul_le prime_prime.pos).2
    dsimp only [active,totalVolume,units]
    rw [rowCount]
    convert density using 1 <;> ring
  rw [min_eq_left payload]
  dsimp only [active,totalVolume]
  rw [rowCount,← Nat.mul_sub]
  generalize h : prime^(r*r)-units = padding
  have classes := Nat.sub_add_cancel unitsLe
  rw [h] at classes
  rw [← classes]
  ring

omit [M8.Machine.Net] in
theorem anchorPayloadCost (d A w W H records : ℕ) :
    let volume := (prime^(w+1))^(d+1)*W
    let anchor := max (Record.cost d A 1 (w+1) W false) (Record.cost d A 1 (w+1) W true) + 2
    let common := anchor + 4 + ((d+1)*(d+1)*(4*H+4)+1) + 4
    records*common + 8*(records*volume) =
      records*(size d+3*A+34+(d+1)*(d+1)*(4*H+4)) + (anchorVolumeRate d A+4)*(records*volume) := by
  intro volume anchor common
  unfold common anchor Record.cost anchorVolumeRate
  simp only [ActualAffineScaling.modulus,Nat.mul_one]
  dsimp only [volume]
  rcases le_total (AtomSegment.chainConst (anchorOps d false)) (AtomSegment.chainConst (anchorOps d true)) with h | h
  · rw [max_eq_right h,max_eq_right (by gcongr)]
    ring
  · rw [max_eq_left h,max_eq_left (by gcongr)]
    ring

noncomputable def exchangePayloadRate (U : Type) {m : ℕ} (j i : ℕ) (k t : Fin m)
    (width w : ℕ) : ℕ :=
  let rates := exchangeTime_le_setup_add_width_volume U j i k t width
  rates.choose*swapVolumeRate w+rates.choose_spec.choose

theorem exchangeScheduleBound (U : Type) {m n : ℕ} (js is : Fin n → ℕ) (ks ts : Fin n → Fin m)
    (width : Fin n → ℕ) (w W H J : ℕ) (xs : List (Fin n)) :
    let cost := fun x a => exchangeTime U (js a) (is a) (ks a) (ts a) (width a) w x H J
    let rate := fun a => exchangePayloadRate U (js a) (is a) (ks a) (ts a) (width a) w
    (xs.map (cost W)).sum ≤ (xs.map (cost 0)).sum+(xs.map rate).sum*((prime^(w+1))^m*W) := by
  intro cost rate
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := (exchangeTime_le_setup_add_width_volume U (js a) (is a) (ks a) (ts a) (width a)).choose_spec.choose_spec w W H J
    change cost W a ≤ cost 0 a + rate a*((prime^(w+1))^m*W) at h
    simp only [List.map_cons,List.sum_cons,Nat.add_mul]
    omega

def cleanupTime (d H total push steps column : ℕ) : ℕ :=
  let stage := 1+column+((d+1)*(d+1)*(4*H+4)+1)
  let rewind := 1+(((d+1)*(4*H+4)+1+(d*(4*H+4)+1))+((d+1)*stage+1))
  let bound := steps+1+rewind
  bound+(total*4+1+total*(6*(push*bound)))

omit [M8.Machine.Net] in
theorem cleanupTime_le (d H total push steps column setup largest forward reverse volume : ℕ)
    (hs : steps ≤ setup+forward*volume) (hc : column ≤ largest+reverse*volume) :
    cleanupTime d H total push steps column ≤ cleanupTime d H total push setup largest +
      ((1+6*total*push)*(forward+(d+1)*reverse))*volume := by
  calc
    _ ≤ cleanupTime d H total push (setup+forward*volume) (largest+reverse*volume) := by
      dsimp only [cleanupTime]
      gcongr
    _ = _ := by dsimp only [cleanupTime]; ring

noncomputable def columnPayloadRate (U : Type) (d w : ℕ) : ℕ :=
  let rates := columnProgramTime_le_setup_add_width_volume U d
  rates.choose*swapVolumeRate w+rates.choose_spec.choose

theorem columnPayloadRate_spec (U : Type) (d w : ℕ) (i j : Fin d) (W H J : ℕ) :
    columnProgramTime U i j w W H J ≤ columnProgramTime U i j w 0 H J +
      columnPayloadRate U d w*((prime^(w+1))^d*W) :=
  (columnProgramTime_le_setup_add_width_volume U d).choose_spec.choose_spec i j w W H J

theorem columnPayloadBound (U : Type) (d w W H J : ℕ) (pivots : Fin (d+1) → Fin (d+1)) :
    let largest := Finset.univ.sup fun j : Fin (d+1) => Finset.univ.sup fun i => columnProgramTime U i j w 0 H J
    (Finset.univ.sup fun i => columnProgramTime U i (pivots i) w W H J) ≤
      largest + columnPayloadRate U (d+1) w*((prime^(w+1))^(d+1)*W) := by
  intro largest
  apply Finset.sup_le
  intro i _
  apply (columnPayloadRate_spec U (d+1) w i (pivots i) W H J).trans
  apply Nat.add_le_add_right
  exact (Finset.le_sup (f := fun k => columnProgramTime U k (pivots i) w 0 H J) (Finset.mem_univ i)).trans
    (Finset.le_sup (f := fun j => Finset.univ.sup fun k => columnProgramTime U k j w 0 H J) (Finset.mem_univ (pivots i)))

omit [M8.Machine.Net] in
theorem physicalScanTime_le {r w W A H : ℕ} (desc : RecursiveInterchangeLayout.Descriptor) (B numRecords : ℕ)
    (shape : desc.beforeH = B*prime^(r*((w+1)*r))) (records : numRecords = LabelMask.records desc)
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (inputs : ℕ → Array d 1 (w+1) W) (cleanBound : (Fin (d+1) → Fin (d+1)) → ℕ)
    (kernel rate prepTime l : ℕ) (rankPos : 0 < r)
    (kernelBound : ∀ p, cleanBound p ≤ kernel + rate*((prime^(w+1))^(d+1)*W)) :
    let volume := (prime^(w+1))^(d+1)*W
    let stepTime := fun (m : Matrix (Fin r) (Fin r) (ZMod prime)) =>
      (if decide (m.det ≠ 0) then prepTime+((6*volume+6)+(1+cleanBound (classPivots (table m))))
       else 4*(d+1)*(d+1)+1)+(4*volume+4)+((d+1)*(d+1)*(4*H+4)+1)
    let count := desc.beforeRows*desc.rows*B
    let traversal := LabelTraversal.time (prime^w) (r*r) 1+5
    l ≤ (1+(count*traversal+4 +
      (((signedInputs table (w+1) numRecords inputs).map (fun x => Record.cost d A 1 (w+1) W x.1+2)).sum+2) +
      (2*(numRecords*(ActualAffineScaling.modulus (w+1)^((d+1)*1)*W))+2))) + 2*(count*traversal+4) +
      (((List.range numRecords).map fun j => stepTime (LabelStock.residue r (w+1) 1 j)+4).sum+2+(2*(numRecords*volume)+2)) →
    let units := ∏ i : Fin r, (prime^r-prime^i.val)
    let common := size d+3*A+34+(d+1)*(d+1)*(4*H+4)
    let live := prepTime + 6 + (1+kernel)
    let pad := 4*(d+1)*(d+1)+1
    let active := count*(prime^w)^(r*r)*units
    let payload := numRecords*volume
    l ≤ 3*count*traversal + (numRecords*common + active*live + (numRecords-active)*pad + (anchorVolumeRate d A+4)*payload +
      (6+rate)*min (active*volume) (((prime-1)*payload)/prime))+21 := by
  intro volume stepTime count traversal time
  let copies := (desc.beforeRows*desc.rows*B)*(prime^w)^(r*r)
  let classes := LabelSelectors.classes 1 (r*r)
  let anchorCost := anchorClassCost table A w W
  let scanCost := fun x => stepTime (LabelSelectors.matrix r x)+4
  have anchors : ((signedInputs table (w+1) numRecords inputs).map (fun x => Record.cost d A 1 (w+1) W x.1+2)).sum =
      copies*(classes.map anchorCost).sum := by
    simpa only [copies,classes,anchorCost,signedInputs,List.map_map,Function.comp_def,records,
      LabelSelectors.residue_eq,LabelSelectors.recordMap,anchorClassCost] using
      LabelSelectors.recordMap_sum desc r w B shape anchorCost
  have scans : ((List.range numRecords).map fun j => stepTime (LabelStock.residue r (w+1) 1 j)+4).sum =
      copies*(classes.map scanCost).sum := by
    simpa only [copies,classes,scanCost,records,LabelSelectors.residue_eq,LabelSelectors.recordMap] using
      LabelSelectors.recordMap_sum desc r w B shape scanCost
  rw [Nat.mul_one (d+1)] at time
  rw [anchors,scans] at time
  have scanPaid : l ≤ 3*count*traversal + count*(prime^w)^(r*r)*(classes.map fun x => anchorCost x + scanCost x).sum +
      4*(numRecords*volume)+21 := by
    apply time.trans_eq
    exact signedClassTime count traversal copies (numRecords*volume) classes anchorCost scanCost
  have classBound := uniformResidualClassBound (w := w) (W := W) (A := A) (H := H) table cleanBound (kernel+rate*volume) volume prepTime
    kernelBound
  have scanTotal := scanPaid.trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ classBound) _) _) _)
  have rowsEq : numRecords = copies*prime^(r*r) := by
    rw [records,LabelMask.records,shape]
    dsimp only [copies]
    rw [show r*((w+1)*r) = (w+1)*(r*r) by ring,pow_mul,pow_succ',mul_pow]
    ring
  let anchor := max (Record.cost d A 1 (w+1) W false) (Record.cost d A 1 (w+1) W true) + 2
  let common := anchor + 4 + ((d+1)*(d+1)*(4*H+4)+1) + 4
  let live := prepTime + 6 + (1+kernel)
  let pad := 4*(d+1)*(d+1)+1
  have commonEq : anchor + (4*volume+4) + ((d+1)*(d+1)*(4*H+4)+1) + 4 = common+4*volume := by unfold common; omega
  have liveEq : prepTime+((6*volume+6)+(1+(kernel+rate*volume))) = live+(6+rate)*volume := by unfold live; ring
  rw [commonEq,liveEq,Nat.add_assoc (3*_*_) (_*_) (4*_),
    physicalPayloadBill r copies volume common live pad (6+rate) numRecords rankPos rowsEq] at scanTotal
  have movement := anchorPayloadCost d A w W H numRecords
  change numRecords*common + 8*(numRecords*volume) = _ at movement
  let active := copies*(∏ i : Fin r, (prime^r-prime^i.val))
  apply scanTotal.trans_eq
  calc
    _ = 3*count*traversal + ((numRecords*common + 8*(numRecords*volume)) +
        active*live + (numRecords-active)*pad + (6+rate)*min (active*volume) (((prime-1)*(numRecords*volume))/prime)) + 21 := by
          dsimp only [active,copies,count]; ac_rfl
    _ = _ := by
      rw [movement]
      dsimp only [active,copies,count,volume,live,pad]
      ac_rfl

/-- One program generates the physical matrix archive, signs the payloads and applies the residual pass. -/
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
      ∀ (registers : Fin ((36+2*r+1+(conjugationDepth r+1)*13)+3) ↪ Fin T)
        (e : (Fin r ⊕ Fin r) ≃ Fin (d+1)),
      let generatorSize := 36+2*r+1+(conjugationDepth r+1)*13
      let generatorHost := QueueLayout.block (n := generatorSize) 0 (by dsimp [generatorSize]; omega) registers
      let control := QueueLayout.block (n := 3) generatorSize (Nat.le_refl _) registers
      let generatorMask := control 0
      let seed := control 1
      let generatorTmp := control 2
      let generatorBank := QueueLayout.block (n := 18) 0 (by omega) generatorHost
      let recip := QueueLayout.block (n := 16) 18 (by omega) generatorHost
      let counters := QueueLayout.block (n := 2) 34 (by omega) generatorHost
      let clock := counters 0
      let generatorCount := counters 1
      let pool := QueueLayout.block (n := (conjugationDepth r+1)*13) (36+2*r+1) (by omega) generatorHost
      let coeff := fun i j : Fin r => (coefficientSlots i j).trans generatorHost
      let generatorArchive := generatorHost ⟨36+2*r, by omega⟩
      have archiveOff : ∀ i, generatorBank (QueueLayout.directoryWork i) ≠ generatorArchive := fun i h => by
        have eq := congrArg Fin.val (generatorHost.injective h)
        change 0 + i.val = 36+2*r at eq
        omega
      have coeffOff : ∀ i j k l, recip k ≠ coeff i j l := fun i j k l h => by
        have eq := congrArg Fin.val (generatorHost.injective h)
        exact reciprocal_ne_coefficient i j k l eq
      let scan := QueueLayout.scanPorts (QueueLayout.directoryWork.trans generatorBank) generatorArchive archiveOff
      scan 4 = tapes 34 → generatorMask ≠ parentTape → scan 2 ≠ parentTape →
      (parents :: scratch :: (slots rs ++ [generatorMask])).Nodup →
      ∀ (dir : Fin 15 ↪ Fin T), dir 14 = generatorBank 2 → dir 0 ≠ parentTape → dir 14 ≠ parentTape →
      generatorMask ≠ dir 14 → dir 9 = parents → parents ≠ tapes 34 →
      (∀ i ∈ ([4,10,11,12] : List (Fin 15)), dir i ≠ parentTape) →
      ∀ (atom unit : Fin T), (∀ i, atom ≠ dir i) → (∀ i, unit ≠ dir i) →
      [unit,atom,dir 7,dir 2,dir 3,dir 5].Nodup → (dir 7 :: dir 2 :: slots rs).Nodup →
      (∀ k ∈ scratch :: slots rs, k ≠ dir 14 ∧ k ≠ tapes 34) →
      parentTape ∉ rs.map Prod.fst → dir 7 ≠ parentTape →
      ∀ (beforeRows rowsTape beforeH : Fin T),
      [beforeRows,rowsTape,beforeH,atom,dir 2,dir 9,dir 3,dir 5].Nodup → dir 9 ≠ parentTape →
      ∃ prog : Pr P T Q prime U, ∀ {w W : ℕ} (baseData : ScanData r d w W) (parent : Fin d → (ZMod (prime^(w+1)))ˣ)
        (proj : Matrix (Fin r) (Fin r) ℚ) (α α' : Fin r → ZMod (prime^(w+1))),
      proj*proj = proj → IntegerMultBounds.Swap.Modular.Admissible prime proj → (∀ i, α i * α' i = 1) →
      let a := baseData.physical e proj α α'
      a.table = table →
      ∀ (inputs : ℕ → Array d 1 (w+1) W),
      (∀ j < a.records, scalarArray (inputs j) = SparseRoleCircuit.encode ∘ a.input j) →
      a.signed = (List.range a.records).map inputs →
      (∀ j < a.records, LabelStock.live r (w+1) 1 j = false →
        ∃ symbol, scalarArray (inputs j) = fun _ => symbol) →
      (prime^(w+1)) < 2^a.H → W < 2^a.J → 0 < W →
      let H := a.H
      let J := a.J
      let cost := fun x a => exchangeTime U (j a).val (i a).val (k a) (t a) (width a) w x H J
      let steps := fun x => ((List.finRange n).map (cost x)).sum
      let push := Fast.Main.mnProgPush residual
      let forward := ((List.finRange n).map fun a => exchangePayloadRate U (j a).val (i a).val (k a) (t a) (width a) w).sum
      let volume := (prime^(w+1))^(d+1)*W
      let prepTime := (d+1)*(2*(d+1)+(4*w+4+columnTime (d+1) prime w H))+1 +
        (d*(8*((d+1)*(d+1)*H)+14*H+22)+1)+(6*H+6)+(4*((d+1)*H)+4)+(6*(d*H)+6)
      ∀ (word : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
        (desc : RecursiveInterchangeLayout.Descriptor) (B : ℕ) (v : HS T Q prime U) (raw : Stacks T prime),
      desc.Positive → (raw.R beforeRows).length = desc.beforeRows → (raw.R rowsTape).length = desc.rows →
      (raw.R beforeH).length = desc.beforeH → raw.R (dir 9) = [] →
      let inputState := installMask raw (dir 9) (List.replicate (desc.beforeRows*desc.rows*B) tick)
      let boxes := (inputState.R (dir 9)).length
      let box := (prime^(w+1))^(r*r)
      let labelWidth := (w+1)*(r*r)
      let prefixWidth := (inputState.R (dir 1)).length
      inputState.R atom = List.replicate (w+1) tick → (inputState.R unit).length = 1 →
      inputState.R (dir 0) = (List.range boxes).flatMap word ++ tail →
      (∀ i < boxes, (word i).length = prefixWidth) →
      (∀ i ∈ ([2,3,4,5,6,7,10,11,12,13] : List (Fin 15)), inputState.R (dir i) = []) →
      let counted := {inputState with R := Function.update (LabelDirectorySetup.prepared inputState.R dir labelWidth) (dir 12) (expandedMask box (fun _ => false) (inputState.R (dir 9)))}
      let ancestor := fun k => word (k/box)
      let directoryWord := (List.range a.records).flatMap (LabelDirectory.entry ancestor r (w+1))
      let built := installMask (installMask counted (dir 0) tail) (dir 14) (directoryWord ++ inputState.R (dir 14))
      let projector := IntegerMultBounds.Swap.Modular.reduce (prime^(w+1)) proj
      let padWord := matrixWords prime H (1 : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod (prime^(w+1))))
      (∀ k ∈ slots rs, built.R k = []) →
      let originalState := {built with R := LabelCountBank.fill (rs.map Prod.fst) (prime^w) (Function.update built.R (dir 7) (List.replicate (prime^w) tick))}
      originalState.R generatorMask = [] →
      originalState.R scratch = [] →
      let bits := (LabelMask.selectors r (w+1) a.records).map (bitSymbol (a := prime))
      let maskedState := installMask originalState generatorMask bits
      maskedState.R (generatorBank 17) = [] →
      let unitWord := binSyms (A := prime) H (1 : ZMod (prime^(w+1))).val
      let unitState := installMask maskedState (generatorBank 17) unitWord
      unitState.R (generatorBank 9) = [] →
      let zeroState := installMask unitState (generatorBank 9) (binSyms H 0)
      zeroState.R seed = [] →
      let seeded := installMask zeroState seed padWord
      ∀ (_tmpBlank : seeded.R generatorTmp = [])
      (_weightBank : seeded.R (recip 13) = [] ∧ ∀ i j, let s := coeff i j
        seeded.R (s 1) = binSyms H (α i).val ∧ seeded.R (s 2) = binSyms H (α' j).val)
      (_ready :
        (∀ i : Fin 18, i ∈ [0,3,4,5,6,7,11,14,15] → seeded.R (generatorBank i) = []) ∧ (seeded.R (generatorBank 8)).length = H ∧
        seeded.R (generatorBank 10) = [] ∧
         (seeded.R clock).length = w ∧ seeded.R generatorCount = [] ∧ seeded.R (recip 14) = [] ∧
        seeded.R (recip 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ seeded.R (recip 4) = binSyms H (prime^(w+1)) ∧
        (∀ i : Fin 16, i ≠ 4 → i < 13 → seeded.R (recip i) = []) ∧
        (∀ k ≤ conjugationDepth r, seeded.R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
        (∀ k ≤ conjugationDepth r, ∀ i : Fin 13, i ≠ 2 → seeded.R (frame pool k i) = []) ∧
        (∃ suffix, seeded.R (generatorBank 16) = matrixWords prime H projector ++ suffix))
      (_prefixWidth : 0 < a.records → (seeded.R (generatorBank 12)).length = prefixWidth)
      (_width : (seeded.R (generatorBank 1)).length = w+1) (_empty : seeded.R (generatorArchive) = [])
      (_output : seeded.R (generatorBank 13) = []),
      let S := queueResult maskedState generatorMask (scan 2) (tapes 34) (inputState.R (dir 14)) (a.matrices 0)
      a.records = LabelMask.records desc → desc.beforeH = B*prime^(r*((w+1)*r)) →
      a.outputTail = [] → S.R (ext 0) = [] →
      let D := embStk anchor S
      Ready d 1 (w+1) W D → LabelTraversal.ready (prime^w) D.R ars → D.R asaved = [] →
      (D.R ap).length = desc.beforeRows*desc.rows*B →
      (D.R (port d regs 0)).length = ActualAffineScaling.modulus (w+1)^((d+1)*1)*W →
      (∀ i ∈ ([2,3,4,5] : List (Fin 6)), D.R (port d regs i) = []) →
      S.R src = ((List.range a.records).map inputs).flatMap payloadWord ++ a.inputTail →
      (S.R (ext 1)).length = volume → S.R (ext 3) = [] → S.R (ext 4) = [] → S.R acc = [] →
      S.R pivot = a.pivotTail →
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
        F.R parentTape = raw.R parentTape ∧ (∀ h, F.L (host (privateBank h)) = [] ∧ F.R (host (privateBank h)) = []) ∧
        let units := ∏ i : Fin r, (prime^r-prime^i.val)
        let active := boxes*(prime^w)^(r*r)*units
        let payload := a.records*volume
        let largest := Finset.univ.sup fun j : Fin (d+1) => Finset.univ.sup fun i => columnProgramTime U i j w 0 H J
        let kernel := cleanupTime d H total push (steps 0) largest
        let rate := (1+6*total*push)*(forward+(d+1)*columnPayloadRate U (d+1) w)
        let common := size d+3*A+34+(d+1)*(d+1)*(4*H+4)
        let live := prepTime + 6 + (1+kernel)
        let pad := 4*(d+1)*(d+1)+1
        l ≤ passPreparationCost desc r (d+1) w B prefixWidth H +
          (3*boxes*(LabelTraversal.time (prime^w) (r*r) 1+5) +
            (a.records*common + active*live + (a.records-active)*pad + (anchorVolumeRate d A+4)*payload +
              (6+rate)*min (active*volume) (((prime-1)*payload)/prime))+21) ∧
        Exec body prog (mk v raw) l (mk z F) := by
  intro rows reads n k j t i width total ports shared bank program spare off reverseHost reverseBank active pop rewind residual privateBank host ext outside parentTape parentOff parentExt body scanPorts tapes src acc pivot rs sizeRs parents scratch maskRegs pivotRegs regs anchor ars ap asaved acap asize alayout banks external sharedSrc anchorParent counters registers e generatorSize generatorHost control generatorMask seed generatorTmp generatorBank recip generatorCounters clock generatorCount pool coeff generatorArchive archiveOff coeffOff scan aligned maskOffParent directoryOffParent genMaskRegs dir dirOut dirSrcParent dirOutParent maskOffDir parentPort parentArchive countParent atom unit atomOff unitApart highLayout highSlots traversalOff parentOutside highParent beforeRows rowsTape beforeH dimensions countOffParent
  obtain ⟨pass,runPass⟩ := archivedPass_exec (U := U) table capacity signCapacity host ext outside parentTape parentOff parentExt body
    rs sizeRs parents scratch maskRegs pivotRegs regs anchor ars ap asaved acap asize alayout banks external sharedSrc anchorParent counters
  let generate : Pr P T Q prime U := seededQueueBody r d e generatorBank recip clock generatorCount pool coeff coeffOff scan generatorMask seed generatorTmp
  obtain ⟨maskWriter,writeMask⟩ := record_writes (body := body) r rs sizeRs generatorMask parents scratch genMaskRegs
  let writeSeed : Pr P T Q prime U := identitySeed (d+1) (generatorBank 9) (generatorBank 17) seed (generatorBank 4) generatorTmp
  let writeZero : Pr P T Q prime U := umulSym 1 (bitSymbol false) (generatorBank 8) (generatorBank 9) (generatorBank 4)
  let copyOne : Pr P T Q prime U := bcopy (recip 15) (generatorBank 17) (generatorBank 4) generatorTmp
  have apart (i j) : generatorHost i ≠ control j := QueueLayout.block_ne _ _ registers (by omega) i j
  have copyPorts (k : Fin 18) (hk : k ≠ 4) : [generatorBank k,seed,generatorBank 4,generatorTmp].Nodup :=
    seedCopyPorts generatorBank control (fun _ _ => apart _ _) k hk
  let buildDirectory : Pr P T Q prime U := .seq (LabelDirectorySetup.setup r dir atom unit)
    (.seq (expandMask (dir 9) (dir 4) (dir 2) (dir 3) (dir 5) (dir 12) (fun _ => false)) (LabelDirectoryBuild.program dir))
  let countBoxes : Pr P T Q prime U := LabelSpectators.program r beforeRows rowsTape beforeH atom (dir 2) (dir 9) (dir 3) (dir 5)
  let prepareCounters : Pr P T Q prime U := .seq (LabelCounts.highCount unit atom (dir 7) (dir 2) (dir 3) (dir 5))
    (scanR (dir 7) (dir 2) (LabelCountBank.pushAll (rs.map Prod.fst)))
  refine ⟨.seq (.seq (.seq countBoxes buildDirectory) prepareCounters) (.seq (.seq maskWriter (.seq (.seq copyOne (.seq (.seq writeZero (.seq (.seq writeSeed generate) (bclear seed))) (bclear (generatorBank 9)))) (bclear (generatorBank 17)))) pass),?_⟩
  intro w W baseData parent proj α α' idem adm inverse a tables inputs encoded unsigned padding hm hw hW H J cost steps push forward volume prepTime
  subst table
  have liveSpec := fun j (_ : j < a.records) => baseData.physical_live e proj idem adm α α' inverse j
  intro word tail desc B rawUser raw positiveDescriptor beforeRowsSize rowsSize beforeHSize parentBlank inputState boxes box labelWidth prefixWidth atomWidth unitWidth parentQueue prefixLen dirFree counted ancestor directoryWord built projector padWord emptySlots originalState maskBlank maskScratch genBits maskedState oneBlank unitWord unitState zeroBlank zeroState seedBlank seeded tmpBlank weightBank generatorReady parentWidth width0 archiveEmpty genOutput init records shape fresh emptyInit anchorView neutral aradix afree acount awidth clean queueInit extCount savedEmpty tmpEmpty accEmpty pivotTail modWord widthWord one padded ticks scratchFree payloadBlank sharedFree parentWord privateFree output

  have parentSize : boxes = desc.beforeRows*desc.rows*B := by simp [boxes,inputState,installMask]
  have rowCount : a.records = boxes*box := by
    rw [records,LabelMask.records,shape,parentSize]
    dsimp only [box]
    rw [← pow_mul,show r*((w+1)*r) = (w+1)*(r*r) by ring]
    simp only [Nat.mul_assoc]
  have counterFrame (k : Fin T) (off : k ∉ rs.map Prod.fst) (high : k ≠ dir 7) :
      originalState.R k = built.R k := by simp [originalState,LabelCountBank.fill,off,high]
  have fstSlot {k} (mem : k ∈ rs.map Prod.fst) : k ∈ slots rs := by
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp mem
    exact List.mem_flatMap.mpr ⟨p,hp,by simp⟩
  have parentOutsideSlots : parents ∉ slots rs := fun mem => genMaskRegs.notMem (by simp [mem])
  have parentFrame := counterFrame parents (fun h => parentOutsideSlots (fstSlot h))
    (parentPort ▸ dir.injective.ne (by decide : (9 : Fin 15) ≠ 7))
  have maskCount : (originalState.R parents).length = desc.beforeRows*desc.rows*B := by
    rw [parentFrame]
    simpa only [← parentPort,built,installMask,counted,LabelDirectorySetup.prepared,
      Function.update_of_ne (dir.injective.ne (by decide : (9 : Fin 15) ≠ 14)),
      Function.update_of_ne (dir.injective.ne (by decide : (9 : Fin 15) ≠ 0)),
      Function.update_of_ne (dir.injective.ne (by decide : (9 : Fin 15) ≠ 4)),
      Function.update_of_ne (dir.injective.ne (by decide : (9 : Fin 15) ≠ 10)),
      Function.update_of_ne (dir.injective.ne (by decide : (9 : Fin 15) ≠ 11)),
      Function.update_of_ne (dir.injective.ne (by decide : (9 : Fin 15) ≠ 12))] using parentSize
  have parentMask : parents ≠ generatorMask := (List.nodup_cons.mp genMaskRegs).1 ∘
    (fun eq => by simp [eq])
  have parentDirectory : parents ≠ scan 2 := by
    change parents ≠ generatorBank 2
    rw [← dirOut,← parentPort]
    exact dir.injective.ne (by decide)
  have countInit : (init.R parents).length = desc.beforeRows*desc.rows*B := by
    simpa only [init,queueResult,maskedState,installMask,Function.update_of_ne parentArchive,
      Function.update_of_ne parentDirectory,Function.update_of_ne parentMask] using maskCount
  have rankPos : 0 < r := by
    rcases e.symm 0 with i | i <;> exact Nat.zero_lt_of_lt i.isLt
  have pos : 0 < labelWidth := Nat.mul_pos (Nat.succ_pos _) (Nat.mul_pos rankPos rankPos)
  have widths (j : ℕ) (inside : j < a.records) : (seeded.R (generatorBank 12)).length = (ancestor j).length := by
    have parentInside : j / box < boxes := (Nat.div_lt_iff_lt_mul (pow_pos (pow_pos prime_prime.pos _) _)).mpr
      (rowCount ▸ inside)
    exact (parentWidth (Nat.zero_lt_of_lt inside)).trans (prefixLen _ parentInside).symm
  have genBlank := generatorReady.1 4 (by simp)
  have rawWidth : (raw.R atom).length = w+1 := by
    simpa only [inputState,installMask,Function.update_of_ne (atomOff 9),List.length_replicate] using congrArg List.length atomWidth
  obtain ⟨inputUser,parentSteps,parentUser,parentBound,parentRun⟩ := LabelSpectators.runs body r rankPos
    beforeRows rowsTape beforeH atom (dir 2) (dir 9) (dir 3) (dir 5) dimensions desc positiveDescriptor
    (w+1) B shape rawUser raw beforeRowsSize rowsSize beforeHSize rawWidth (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · simpa [inputState,installMask] using dirFree 2 (by decide)
      · exact parentBlank
      · simpa [inputState,installMask] using dirFree 3 (by decide)
      · simpa [inputState,installMask] using dirFree 5 (by decide))
  obtain ⟨builtUser,dirSteps,dirUser,dirBound,dirExec⟩ := LabelDirectorySetup.build_from_parents (body := body)
    r dir atom unit atomOff unitApart inputUser inputState word tail unitWidth dirFree
      (by simpa only [atomWidth,List.length_replicate] using pos) parentQueue prefixLen
  have boxSize : prime^labelWidth = box := pow_mul ..
  simp only [atomWidth,List.length_replicate] at dirBound dirExec
  change dirSteps ≤ 8*(w+1)+8+22*(prime^labelWidth) + (boxes*(6*(prime^labelWidth)+10)+6 +
    (boxes*(prime^labelWidth)*(9*labelWidth+15)+6 + (boxes*((prime^labelWidth)*(8*prefixWidth+11)+6*prefixWidth+15)+6 +
      boxes*(prime^labelWidth)*(6*(prefixWidth+labelWidth)+13)+6))) at dirBound
  rw [boxSize] at dirBound
  have dirRun : Exec body buildDirectory (mk inputUser inputState) dirSteps (mk builtUser built) := by
    simpa only [built,counted,installMask,directoryWord,ancestor,rowCount,← boxSize,labelWidth,boxes] using dirExec
  have retained (k) (off : ∀ i, k ≠ dir i) : built.R k = inputState.R k := by
    simp [built,installMask,counted,LabelDirectorySetup.prepared,Function.update_of_ne (off _)]
  obtain ⟨maskRadix,original,initSteps,initUser,initBound,initializeRun⟩ :=
    LabelCountBank.prepare_exec body rs unit atom (dir 7) (dir 2) (dir 3) (dir 5) highLayout highSlots
      builtUser built (w+1) (by omega) ((retained atom atomOff).trans atomWidth)
      ((congrArg List.length (retained unit unitApart)).trans unitWidth) (by
        intro k hk
        rcases List.mem_append.mp hk with h | h
        · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
          rcases h with rfl | rfl | rfl | rfl <;> simp [built,installMask,counted,LabelDirectorySetup.prepared,dirFree]
        · exact emptySlots k h)
  have directoryFrame := counterFrame (dir 14)
    (fun h => (traversalOff _ (List.mem_cons_of_mem _ (fstSlot h))).1 rfl) (dir.injective.ne (by decide))
  have directory : maskedState.R (generatorBank 2) = directoryWord ++ inputState.R (dir 14) := by
    rw [← dirOut]
    exact (Function.update_of_ne maskOffDir.symm _ _).trans (directoryFrame.trans (Function.update_self ..))
  obtain ⟨masked,maskSteps,maskUser,maskBound,maskExec⟩ :=
    writeMask desc (w+1) B (by omega) shape original originalState ⟨by simpa using maskRadix,maskScratch,maskCount⟩
  have maskRun : Exec body maskWriter (mk original originalState) maskSteps (mk masked maskedState) := by
    simpa only [maskedState,installMask,genBits,← records,maskBlank,List.append_nil] using maskExec
  have genMask : maskedState.R generatorMask = (List.range a.records).map fun j => bitSymbol (LabelStock.live r (w+1) 1 j) := by
    simpa only [genBits,LabelMask.selectors,List.map_map,Function.comp_def] using
      (show maskedState.R generatorMask = genBits from Function.update_self ..)
  have kept (k : Fin 18) : seeded.R (generatorBank k) = zeroState.R (generatorBank k) :=
    Function.update_of_ne (apart _ 1) _ _
  have tmpKept : seeded.R generatorTmp = zeroState.R generatorTmp :=
    Function.update_of_ne (control.injective.ne (by decide : (2 : Fin 3) ≠ 1)) _ _
  have unchanged (k : Fin 18) (hk : k ≠ 9) : zeroState.R (generatorBank k) = unitState.R (generatorBank k) :=
    Function.update_of_ne (generatorBank.injective.ne hk) _ _
  have zeroWidth := (congrArg List.length ((kept 8).trans (unchanged 8 (by decide)))).symm.trans generatorReady.2.1
  have beforeCopy (k : Fin 18) (hk : k ≠ 17) : unitState.R (generatorBank k) = maskedState.R (generatorBank k) :=
    Function.update_of_ne (generatorBank.injective.ne hk) _ _
  have sep (i j) : generatorBank i ≠ recip j := QueueLayout.block_ne _ _ generatorHost (by decide) i j
  have unitSource : maskedState.R (recip 15) = unitWord := by
    simpa only [seeded,zeroState,unitState,installMask,Function.update_of_ne (show recip 15 ≠ seed from apart _ 1),
      Function.update_of_ne (sep 9 15).symm,Function.update_of_ne (sep 17 15).symm] using generatorReady.2.2.2.2.2.2.1
  have copyScratch := ((kept 4).trans (unchanged 4 (by decide))).symm.trans genBlank
  obtain ⟨copied,copyUser,copyRun⟩ := unitCopy_exec body generatorBank (recip 15) generatorTmp
    (fun i => (sep i 15).symm) (fun _ => apart _ 2) (apart _ 2)
    masked maskedState unitWord unitSource oneBlank ((beforeCopy 4 (by decide)).symm.trans copyScratch) (by
      simpa only [zeroState,unitState,installMask,Function.update_of_ne (show generatorTmp ≠ generatorBank 9 from (apart _ 2).symm),
        Function.update_of_ne (show generatorTmp ≠ generatorBank 17 from (apart _ 2).symm)] using tmpKept.symm.trans tmpBlank)
  have unitLen : unitWord.length = H := length_binSyms ..
  rw [unitLen] at copyRun
  have unitDest : seeded.R (generatorBank 17) = unitWord :=
    (kept 17).trans ((unchanged 17 (by decide)).trans (Function.update_self ..))
  obtain ⟨withZero,zeroUser,zeroRun⟩ := umulSym_exec body 1 (bitSymbol false)
    (a := generatorBank 8) (b := generatorBank 9) (t := generatorBank 4) (by simp) (by simp) (by simp) copied unitState copyScratch
  have zeroCode : (binSyms H 0 : List (Fin (prime+4))) = List.replicate H (bitSymbol false) := by
    simp [binSyms,List.ofFn_const]
  rw [zeroWidth,Nat.one_mul,zeroBlank,List.append_nil,← zeroCode] at zeroRun
  have zeroWord : zeroState.R (generatorBank 9) = binSyms H 0 := Function.update_self ..
  obtain ⟨prepared,seedSteps,seedUser,seedBound,seedRun⟩ := identitySeed_writes (M := prime^(w+1)) body
    (d+1) H (generatorBank 9) (generatorBank 17) seed (generatorBank 4) generatorTmp
    (copyPorts 9 (by decide)) (copyPorts 17 (by decide)) withZero zeroState
    ⟨zeroWord,(kept 17).symm.trans unitDest,(kept 4).symm.trans genBlank,tmpKept.symm.trans tmpBlank⟩
  rw [seedBlank,List.append_nil] at seedRun
  have maskKept : seeded.R generatorMask = maskedState.R generatorMask :=
    (Function.update_of_ne (control.injective.ne (by decide : (0 : Fin 3) ≠ 1)) _ _).trans ((Function.update_of_ne (apart _ 0).symm _ _).trans (Function.update_of_ne (apart _ 0).symm _ _))
  obtain ⟨_,generatedUser,genSteps,genUser,genBound,generated⟩ := physicalResidualQueue_exec body w a.records projector H hm
    registers ancestor (inputState.R (dir 14)) e α α' prepared seeded (Function.update_self ..) tmpBlank weightBank ⟨generatorReady.1,generatorReady.2.1,(kept 9).trans zeroWord,(by
        obtain ⟨_,_,p,c,t,h,o,m,f,ms,fs,pr⟩ := generatorReady
        exact ⟨p,c,t,h,o,m,f,ms,fs,pr,unitDest⟩)⟩ widths width0 genBlank
      archiveEmpty ((kept 2).trans ((unchanged 2 (by decide)).trans ((beforeCopy 2 (by decide)).trans directory))) genOutput (maskKept.trans genMask)
  obtain ⟨liveCount,paddingCount⟩ := residualBranchCounts r w boxes a.records rowCount
  rw [liveCount,paddingCount] at genBound
  let liveRecords := boxes*((∏ i : Fin r, (prime^r-prime^i.val))*(prime^w)^(r*r))
  let price := matrixBuildCost r (d+1) w H + 12*r*r*prefixWidth
  let archiveTime := liveRecords*(price+4*((d+1)*(d+1)*H)) +
    (a.records-liveRecords)*(10*((d+1)*(d+1)*H)+6) +
    a.records*(4*prefixWidth+4+(r*r*(4*(w+1)+4)+1)+6)+4
  have archiveBound : genSteps ≤ archiveTime := by
    by_cases inside : 0 < a.records
    · rw [parentWidth inside,liveRecordCost_width] at genBound
      exact genBound
    · have empty := Nat.eq_zero_of_not_pos inside
      have noLive : liveRecords = 0 := by
        rw [empty] at liveCount
        exact liveCount.symm
      change boxes*_ = 0 at noLive
      simpa only [archiveTime,liveRecords,noLive,empty,Nat.zero_sub,Nat.zero_mul,Nat.zero_add] using genBound
  have padLen : padWord.length = (d+1)*(d+1)*H := length_matrixWords ..
  have seedAndArchive := Nat.add_le_add (Nat.add_le_add seedBound archiveBound)
    (Nat.le_of_eq (congrArg (fun n => 2*n+2) padLen))
  have paid := Nat.add_le_add_right (Nat.add_le_add_left (Nat.add_le_add_right
    (Nat.add_le_add_left seedAndArchive (4*H+4)) (2*H+2)) (6*H+6)) (2*H+2)
  rw [paddingSetupCost_eq] at paid
  have matrixWord := baseData.physical_archive e proj α α'
  let filled := queueResult seeded generatorMask (scan 2) (tapes 34) (inputState.R (dir 14)) (a.matrices 0)
  have genRun : Exec body generate (mk prepared seeded) genSteps (mk generatedUser filled) := by
    dsimp only [filled]
    rw [← aligned,matrixWord]
    exact generated
  obtain ⟨cleared,clearUser,clearRun⟩ := clearQueueSeed_exec body seed generatorMask (scan 2) (tapes 34)
    (control.injective.ne (by decide : (1 : Fin 3) ≠ 0)) (apart _ 1).symm
    (aligned ▸ (show seed ≠ scan 4 from (apart _ 1).symm)) padWord (inputState.R (dir 14))
    (a.matrices 0) generatedUser zeroState seedBlank
  obtain ⟨released,releaseUser,releaseRun⟩ := clearQueueSeed_exec body (generatorBank 9) generatorMask (scan 2) (tapes 34)
    (apart _ 0) (generatorBank.injective.ne (by decide : (9 : Fin 18) ≠ 2))
    (aligned ▸ (show generatorBank 9 ≠ scan 4 from archiveOff 9)) (binSyms H 0) (inputState.R (dir 14))
    (a.matrices 0) cleared unitState zeroBlank
  rw [length_binSyms] at releaseRun
  have unitOff : generatorBank 17 ≠ scan 4 := by
    intro eq
    have bad := congrArg Fin.val (generatorHost.injective eq)
    change 0+17 = 36+2*r at bad
    omega
  obtain ⟨first,finishUser,finishRun⟩ := clearQueueSeed_exec body (generatorBank 17) generatorMask (scan 2) (tapes 34)
    (apart _ 0) (generatorBank.injective.ne (by decide : (17 : Fin 18) ≠ 2))
    (aligned ▸ unitOff) unitWord (inputState.R (dir 14)) (a.matrices 0) released maskedState oneBlank
  rw [unitLen] at finishRun
  have countedParent : counted.R parentTape = inputState.R parentTape := by
    simp only [counted,LabelDirectorySetup.prepared,Function.update_of_ne (countParent 12 (by decide)).symm,
      Function.update_of_ne (countParent 4 (by decide)).symm,Function.update_of_ne (countParent 10 (by decide)).symm,
      Function.update_of_ne (countParent 11 (by decide)).symm]
  have parentKept : init.R parentTape = inputState.R parentTape := by
    exact (Function.update_of_ne (parentOff _).symm _ _).trans
      ((Function.update_of_ne directoryOffParent.symm _ _).trans ((Function.update_of_ne maskOffParent.symm _ _).trans
        ((Function.update_of_ne maskOffParent.symm _ _).trans ((counterFrame parentTape parentOutside highParent.symm).trans ((Function.update_of_ne dirOutParent.symm _ _).trans
          ((Function.update_of_ne dirSrcParent.symm _ _).trans countedParent))))))
  have archive : init.R (tapes 34) = a.matrices 0 := Function.update_self ..

  have traversalFrame (k) (hk : k ∈ scratch :: slots rs) : init.R k = originalState.R k := by
    have hd : k ≠ scan 2 := dirOut ▸ (traversalOff _ hk).1
    have hm : k ≠ generatorMask := by
      rcases List.mem_cons.mp hk with rfl | h
      · exact fun eq => genMaskRegs.tail.notMem (by simp [eq])
      · exact (List.nodup_append.mp genMaskRegs.tail.tail).2.2 k h _ (by simp)
    simp only [init,queueResult,maskedState,installMask,Function.update_of_ne (traversalOff _ hk).2,
      Function.update_of_ne hd,Function.update_of_ne hm]
  have radixInit : LabelTraversal.ready (prime^w) init.R rs := by
    intro p hp
    rw [traversalFrame _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨p,hp,by simp⟩)),
      traversalFrame _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨p,hp,by simp⟩))]
    exact maskRadix p hp
  have scratchInit := (traversalFrame scratch (by simp)).trans maskScratch
  obtain ⟨z,F,l,hz,queue,accEnd,maskEnd,pivots,finalArchive,parentEnd,free,time,run⟩ :=
    runPass a parent rfl inputs encoded unsigned liveSpec padding hm hw hW desc B first init records shape radixInit
      scratchInit countInit fresh emptyInit neutral aradix afree acount awidth clean queueInit extCount savedEmpty tmpEmpty
      accEmpty pivotTail archive modWord widthWord one padded ticks scratchFree payloadBlank sharedFree parentWord privateFree
  let largest := Finset.univ.sup fun j : Fin (d+1) => Finset.univ.sup fun i => columnProgramTime U i j w 0 H J
  let kernel := cleanupTime d H total push (steps 0) largest
  let rate := (1+6*total*push)*(forward+(d+1)*columnPayloadRate U (d+1) w)
  let column := fun (i j : Fin (d+1)) => columnProgramTime U i j w W H J
  let pivotCost := fun (p : Fin (d+1) → Fin (d+1)) => cleanupTime d H total push (steps W) (Finset.univ.sup fun i => column i (p i))
  have schedule := exchangeScheduleBound U (fun a => (j a).val) (fun a => (i a).val) k t width w W H J (List.finRange n)
  have scanTotal := physicalScanTime_le (A := A) (H := H) desc B a.records shape records a.table inputs pivotCost
    kernel rate prepTime l rankPos (fun p => cleanupTime_le d H total push _ _ _ _ _ _ volume schedule
      (columnPayloadBound U d w W H J p)) time
  have prep := residualPreparation_le desc r (d+1) w B prefixWidth H rankPos
    (records ▸ parentSize ▸ rowCount)
  have setupBound := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add parentBound dirBound) initBound)
    (Nat.add_le_add maskBound paid)
  have setupPaid := setupBound.trans (show _ ≤ passPreparationCost desc r (d+1) w B prefixWidth H from by
    simpa only [archiveTime,price,liveRecords,labelWidth,parentSize,records,Nat.add_one_sub_one] using prep)
  have totalBound := Nat.add_le_add setupPaid scanTotal
  rw [Nat.add_assoc (parentSteps+dirSteps+initSteps) _ l] at totalBound
  exact ⟨z,F,_,hz.trans (finishUser.trans (releaseUser.trans (clearUser.trans (genUser.trans (seedUser.trans
      (zeroUser.trans (copyUser.trans (maskUser.trans (initUser.trans (dirUser.trans parentUser)))))))))),queue,accEnd,maskEnd,pivots,finalArchive,
    parentEnd.trans (parentKept.trans (Function.update_of_ne countOffParent.symm _ _)),free,by simpa only [parentSize] using totalBound,
    Exec.seq (Exec.seq (Exec.seq parentRun dirRun) initializeRun) (Exec.seq (Exec.seq maskRun (Exec.seq (Exec.seq copyRun (Exec.seq (Exec.seq zeroRun
      (Exec.seq (Exec.seq seedRun genRun) clearRun)) releaseRun)) finishRun)) run)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
