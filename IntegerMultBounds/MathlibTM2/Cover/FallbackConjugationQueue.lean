module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalConjugation
public import IntegerMultBounds.MathlibTM2.Cover.FallbackQueueLayout
public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaSources
public import IntegerMultBounds.MathlibTM2.Cover.FallbackResidualWord

/-! Generate weighted residual matrices in physical directory order.
The conjugate-only queue can be restored from commit 2c23aa3c. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {P U : Type} {T Q m : ℕ}

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- Maximum frame depth needed to evaluate a conjugate in dimension `m`. -/
noncomputable def conjugationDepth (m : ℕ) : ℕ :=
  max (determinant (matrixInput (m := m) false)).depth
    (Finset.univ.sup fun ij : Fin m × Fin m =>
      (numerator (matrixInput false) (matrixInput true) ij.1 ij.2).depth)

/-- The entry reader shares the directory's constants and indexes one tape per
row weight and column weight. All entries append to the same archive. -/
def coefficientSlots {m extra : ℕ} (i j : Fin m) :
    Fin 4 ↪ Fin (36+2*m+1+extra) :=
  let slots : Fin 4 → Fin (36+2*m+1+extra) := ![
    ⟨if i = j then 17 else 9, by split <;> omega⟩,
    ⟨36+i.val, by omega⟩, ⟨36+m+j.val, by omega⟩, ⟨36+2*m, by omega⟩]
  ⟨slots, by
    intro x y eq
    have h := congrArg Fin.val eq
    fin_cases x <;> fin_cases y <;> simp_all [slots, Matrix.cons_val] <;> (try split_ifs at *) <;> omega⟩

/-- Steps for one live record, including its determinant, conjugation, and residual entries. -/
noncomputable def liveRecordCost (m d w H ancestorWidth numTime detTime : ℕ) : ℕ :=
  let C := 48*H*H+152*H+66
  ((m*(m*(12*ancestorWidth+8*((w+1)*(m*m))+(w+1)*(7*H+prime+31)+10*H+42)+1)+1) + (detTime + (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) +
       ((m*(m*(numTime+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) + (2*(m*m*H)+2)) +
       (d*(d*(8*(m*m*H)+96*H*H+344*H+182)+1)+1)+(2*(m*m*H)+2)

/-- The queue writer is fixed by its register layout and residual coordinates. -/
noncomputable def physicalResidualQueue {d : ℕ}
    (registers : Fin ((36+2*m+1+(conjugationDepth m+1)*13)+3) ↪ Fin T)
    (e : (Fin m ⊕ Fin m) ≃ Fin d) : Pr P T Q prime U :=
    let size := 36+2*m+1+(conjugationDepth m+1)*13
    let host := QueueLayout.block (n := size) 0 (by dsimp [size]; omega) registers
    let control := QueueLayout.block (n := 3) size (Nat.le_refl _) registers
    let mask := control 0
    let seed := control 1
    let tmp := control 2
    let bank := QueueLayout.block (n := 18) 0 (by omega) host
    let r := QueueLayout.block (n := 16) 18 (by omega) host
    let counters := QueueLayout.block (n := 2) 34 (by omega) host
    let clock := counters 0
    let count := counters 1
    let pool := QueueLayout.block (n := (conjugationDepth m+1)*13) (36+2*m+1) (by omega) host
    let coeff := fun i j : Fin m => (coefficientSlots i j).trans host
    let archive := host ⟨36+2*m, by omega⟩
    have archiveOff : ∀ i, bank (QueueLayout.directoryWork i) ≠ archive := fun i h => by
      have eq := congrArg Fin.val (host.injective h)
      change 0 + i.val = 36+2*m at eq
      omega
    have coeffOff : ∀ i j k l, r k ≠ coeff i j l := fun i j k l h => by
      have eq := congrArg Fin.val (host.injective h)
      change 18+k.val = (coefficientSlots (extra := (conjugationDepth m+1)*13) i j l).val at eq
      fin_cases l <;> simp [coefficientSlots, Matrix.cons_val] at eq <;> (try split_ifs at *) <;> omega
    let inputs := QueueLayout.formulaInputs.trans bank
    let source := sourcePorts (m := m) inputs id
    let weights := fun i j => QueueLayout.residualPorts r (coeff i j) (coeffOff i j)
    let scan := QueueLayout.scanPorts (QueueLayout.directoryWork.trans bank) archive archiveOff
    let f := determinant (matrixInput false)
    let conjugate : Pr P T Q prime U := (.seq (directoryMatrix m (QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans bank)) (QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans bank)) (bank 12) (bank 9) (bank 10)) (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse prime r clock count))
        (.seq (packedConjugate pool source (QueueLayout.normalizationPorts.trans r) false true) (.seq (bclear (r 0)) (bclear (r 14))))) (bclear (bank 10))))
    let live : Pr P T Q prime U := .seq conjugate (.seq (sequence (fun i => sequence
      (fun j => blockEntry weights (e.symm i) (e.symm j)) (List.finRange d)) (List.finRange d)) (bclear (r 13)))
    let branch := fun p => Prog.seq p (.seq (moveR (scan 4) (scan 5) id) (advanceDirectory m scan))
    (.seq (maskedScan mask (branch live) (branch (bcopy seed (scan 4) (scan 3) tmp)))
        (moveR (scan 5) (scan 4) id))

theorem physicalResidualQueue_exec (body : P → Pr P T Q prime U)
    (w records : ℕ)
    (projector : Matrix (Fin m) (Fin m) (ZMod (prime^(w+1))))
    (H : ℕ) (hm : prime^(w+1) < 2^H) (registers : Fin ((36+2*m+1+(conjugationDepth m+1)*13)+3) ↪ Fin T) :
    let size := 36+2*m+1+(conjugationDepth m+1)*13
    let host := QueueLayout.block (n := size) 0 (by dsimp [size]; omega) registers
    let control := QueueLayout.block (n := 3) size (Nat.le_refl _) registers
    let mask := control 0
    let seed := control 1
    let tmp := control 2
    let bank := QueueLayout.block (n := 18) 0 (by omega) host
    let r := QueueLayout.block (n := 16) 18 (by omega) host
    let counters := QueueLayout.block (n := 2) 34 (by omega) host
    let clock := counters 0
    let count := counters 1
    let pool := QueueLayout.block (n := (conjugationDepth m+1)*13) (36+2*m+1) (by omega) host
    let coeff := fun i j : Fin m => (coefficientSlots i j).trans host
    let archive := host ⟨36+2*m, by omega⟩
    have archiveOff : ∀ i, bank (QueueLayout.directoryWork i) ≠ archive := fun i h => by
      have eq := congrArg Fin.val (host.injective h)
      change 0 + i.val = 36+2*m at eq
      omega
    have coeffOff : ∀ i j k l, r k ≠ coeff i j l := fun i j k l h => by
      have eq := congrArg Fin.val (host.injective h)
      change 18+k.val = (coefficientSlots (extra := (conjugationDepth m+1)*13) i j l).val at eq
      fin_cases l <;> simp [coefficientSlots, Matrix.cons_val] at eq <;> (try split_ifs at *) <;> omega
    ∀ (ancestor : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    {d : ℕ} (e : (Fin m ⊕ Fin m) ≃ Fin d)
    (α α' : Fin m → ZMod (prime^(w+1))),
    let padWord := matrixWords prime H (1 : Matrix (Fin d) (Fin d) (ZMod (prime^(w+1))))
    ∀ (v : HS T Q prime U) (S : Stacks T prime)
    (_seedWord : S.R seed = padWord) (_tmpBlank : S.R tmp = [])
    (_weightBank : S.R (r 13) = [] ∧ ∀ i j, let s := coeff i j
      S.R (s 1) = binSyms H (α i).val ∧ S.R (s 2) = binSyms H (α' j).val)
    (_ready :
      (∀ i : Fin 18, i ∈ [0,3,4,5,6,7,11,14,15] → S.R (bank i) = []) ∧ (S.R (bank 8)).length = H ∧
      S.R (bank 9) = binSyms H 0 ∧ S.R (bank 10) = [] ∧
       (S.R clock).length = w ∧ S.R count = [] ∧ S.R (r 14) = [] ∧
      S.R (r 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ S.R (r 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (r i) = []) ∧
      (∀ k ≤ conjugationDepth m, S.R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ conjugationDepth m, ∀ i : Fin 13, i ≠ 2 → S.R (frame pool k i) = []) ∧
      (∃ suffix, S.R (bank 16) = matrixWords prime H projector ++ suffix) ∧
      S.R (bank 17) = binSyms H (1 : ZMod (prime^(w+1))).val)
    (_widths : ∀ j < records, (S.R (bank 12)).length = (ancestor j).length)
    (_width : (S.R (bank 1)).length = w+1) (_blank : S.R (bank 4) = []) (_empty : S.R (archive) = [])
    (_directory : S.R (bank 2) = (List.range records).flatMap (LabelDirectory.entry ancestor m (w+1)) ++ tail)
    (_output : S.R (bank 13) = []) (_bits : S.R mask = (List.range records).map fun j => bitSymbol (LabelStock.live m (w+1) 1 j)),
    let inputs := QueueLayout.formulaInputs.trans bank
    let source := sourcePorts (m := m) inputs id
    let weights := fun i j => QueueLayout.residualPorts r (coeff i j) (coeffOff i j)
    let scan := QueueLayout.scanPorts (QueueLayout.directoryWork.trans bank) archive archiveOff
    let num := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    let f := determinant (matrixInput false)
    let conjugate : Pr P T Q prime U := (.seq (directoryMatrix m (QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans bank)) (QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans bank)) (bank 12) (bank 9) (bank 10)) (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse prime r clock count))
        (.seq (packedConjugate pool source (QueueLayout.normalizationPorts.trans r) false true) (.seq (bclear (r 0)) (bclear (r 14))))) (bclear (bank 10))))
    let live : Pr P T Q prime U := .seq conjugate (.seq (sequence (fun i => sequence
      (fun j => blockEntry weights (e.symm i) (e.symm j)) (List.finRange d)) (List.finRange d)) (bclear (r 13)))
    let active := LabelStock.live m (w+1) 1
    let word := fun j => if active j then matrixWords prime H (projectorResidual e projector α α' (physicalLabel m (w+1) j)) else padWord
    let livePrice := liveRecordCost m d w H (S.R (bank 12)).length cost (time H (readTime H) f)
    let branch := fun p => Prog.seq p (.seq (moveR (scan 4) (scan 5) id) (advanceDirectory m scan))
    let words := (List.range records).flatMap word
    words.length = records*(d*d*H) ∧
    ∃ (z : HS T Q prime U) (n : ℕ), z.user = v.user ∧
      n ≤ (List.range records).countP active * (livePrice + 4*(d*d*H)) +
        (List.range records).countP (fun j => !active j) * (10*(d*d*H)+6) +
        records * (4*(S.R (bank 12)).length+4+(m*m*(4*(w+1)+4)+1)+6) + 4 ∧
      Exec body (.seq (maskedScan mask (branch live) (branch (bcopy seed (scan 4) (scan 3) tmp)))
        (moveR (scan 5) (scan 4) id)) (mk v S) n (mk z (queueResult S mask (scan 2) (scan 4) tail words)) := by
  intro size host control mask seed tmp bank r counters clock count pool coeff archive archiveOff coeffOff ancestor tail
    d e α α' padWord v S seedWord tmpBlank weightBank ready
    widths width blank empty directory output bits
  have br (i j) : bank i ≠ r j := QueueLayout.block_ne _ _ host (by decide) i j
  have bp (i j) : bank i ≠ pool j := QueueLayout.block_ne _ _ host (by omega) i j
  have rp (i j) : r i ≠ pool j := QueueLayout.block_ne _ _ host (by omega) i j
  have rc (i j) : r i ≠ counters j := QueueLayout.block_ne _ _ host (by decide) i j
  have copyPorts : [clock,count,r 2,r 3].Nodup := by
    simp [clock,count,counters.injective.eq_iff,(rc _ _).symm,r.injective.eq_iff]
  intro inputs source weights scan num cost f conjugate live active word livePrice
  have apart (i j) : host i ≠ control j := QueueLayout.block_ne _ _ registers (by omega) i j
  have maskOff (k) : mask ≠ scan k := by
    fin_cases k <;> exact (apart _ 0).symm
  have padPorts : [seed,archive,bank 4,tmp].Nodup := by
    have ab : archive ≠ bank 4 := fun h => archiveOff 4 h.symm
    simp [seed,tmp,ab,control.injective.eq_iff,show control 1 ≠ archive from (apart _ _).symm,
      show control 1 ≠ bank 4 from (apart _ _).symm,
      show archive ≠ control 2 from apart _ _,show bank 4 ≠ control 2 from apart _ _]
  have detFits : f.depth ≤ conjugationDepth m := Nat.le_max_left _ _
  have fits (i j : Fin m) : (num i j).depth ≤ conjugationDepth m :=
    le_trans (Finset.le_sup (f := fun ij : Fin m × Fin m => (num ij.1 ij.2).depth)
      (Finset.mem_univ (i,j))) (Nat.le_max_right _ _)
  let workspace := fun R : Regs T prime => ∀ k, k ≠ mask → k ≠ bank 2 → k ≠ bank 13 → R k = S.R k
  have stable : ∀ R M, workspace R →
      (∀ k, k ≠ mask → k ≠ bank 2 → k ≠ bank 13 → M k = R k) → workspace M :=
    fun _ _ ws keep k hm hd ho => (keep k hm hd ho).trans (ws k hm hd ho)
  have keepBank {R} (ws : workspace R) (k : Fin 18) (hd : k ≠ 2) (ho : k ≠ 13) :=
    ws (bank k) (apart _ 0) (bank.injective.ne hd) (bank.injective.ne ho)
  have padReady : ∀ R, workspace R → R seed = padWord ∧ R (bank 4) = [] ∧ R tmp = [] := by
    intro R ws
    have keep (k : Fin 3) (hk : k ≠ 0) :=
      ws (control k) (control.injective.ne hk) (apart _ k).symm (apart _ k).symm
    exact ⟨(keep 1 (by decide)).trans seedWord,(keepBank ws 4 (by decide) (by decide)).trans blank,
      (keep 2 (by decide)).trans tmpBlank⟩
  let price := fun j => if active j then livePrice else 6*padWord.length+6
  have padLen : padWord.length = d*d*H := length_matrixWords ..
  have wordLen (j) : (word j).length = d*d*H := by
    cases h : active j <;> simp [word,h,length_matrixWords,padLen]
  constructor
  · have len (ids : List ℕ) : (ids.flatMap word).length = ids.length*(d*d*H) := by
      induction ids with
      | nil => simp
      | cons j ids ih => simp [wordLen,ih,Nat.add_mul,Nat.add_comm]
    simpa using len (List.range records)
  have ledger (ids : List ℕ) (valid : ∀ j ∈ ids, j < records) :
      (ids.map (fun j => price j+2*(word j).length+2+
        (4*(ancestor j).length+4+(m*m*(4*(w+1)+4)+1))+4)).sum + 2*(ids.flatMap word).length =
      ids.countP active * (livePrice+4*(d*d*H)) +
        ids.countP (fun j => !active j) * (10*(d*d*H)+6) +
        ids.length * (4*(S.R (bank 12)).length+4+(m*m*(4*(w+1)+4)+1)+6) := by
    induction ids with
    | nil => simp
    | cons j ids ih =>
      have bound := ih (fun k hk => valid k (List.mem_cons_of_mem _ hk))
      have widthEq := widths j (valid j List.mem_cons_self)
      cases h : active j <;>
        simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,List.length_cons,
          List.countP_cons, h, Bool.not_true, Bool.not_false, price, wordLen, padLen, Bool.false_eq_true,
          ite_true, ite_false, Nat.add_mul, Nat.mul_add, Nat.one_mul] at * <;> omega
  have total := ledger (List.range records) (fun _ => List.mem_range.mp)
  rw [List.length_range] at total
  have eqCost : ((List.range records).map (fun j => price j+2*(word j).length+2+
      (4*(ancestor j).length+4+(m*m*(4*(w+1)+4)+1))+4)).sum+2+(2*((List.range records).flatMap word).length+2) = _ :=
    (show _ = _ + 4 by omega).trans (congrArg (· + 4) total)
  rw [← eqCost]
  apply directoryQueue_exec body scan mask maskOff m (w+1) records active live seed tmp padPorts padWord price
    ancestor word tail workspace stable padReady (fun j _ h => by simp [word,price,h])
    _ v S (fun _ _ _ _ => rfl) widths width blank empty directory output bits
  intro j hj h u B ⟨ws,rest,headEq⟩
  obtain ⟨scratch,bitWidth,zeroWord,packedBlank,ticks,countBlank,pivot,oneWord,modulus,free,moduli,frames,projTape,inputOne⟩ := ready
  have kb := keepBank ws
  have kr (k : Fin 16) := ws (r k) (apart _ 0) (br 2 k).symm (br 13 k).symm
  have kc (k : Fin 2) := ws (counters k) (apart _ 0)
    (QueueLayout.block_ne _ _ host (by decide) (2 : Fin 18) k).symm
    (QueueLayout.block_ne _ _ host (by decide) (13 : Fin 18) k).symm
  have kf (k i) := ws (frame pool k i) (apart _ 0) (bp 2 _).symm (bp 13 _).symm
  have prefixLen := (congrArg List.length (kb 12 (by decide) (by decide))).trans (widths j hj)
  have digitWidth := (congrArg List.length (kb 1 (by decide) (by decide))).trans width
  have protectedScratch (i : Fin 18) (hi : i ∈ [0,3,4,5,6,7,11,14,15]) : B.R (bank i) = [] := by
    have off : i ≠ 2 ∧ i ≠ 13 := (by decide : ∀ i : Fin 18, i ∈ [0,3,4,5,6,7,11,14,15] →
      i ≠ 2 ∧ i ≠ 13) i hi
    exact (kb i off.1 off.2).trans (scratch i hi)
  have scratchPort : ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 →
      QueueLayout.normalizationPorts k ≠ 4 ∧ QueueLayout.normalizationPorts k < 13 := by decide
  let mat : Bool → Matrix (Fin m) (Fin m) (ZMod (prime^(w+1))) := fun k => if k then projector else physicalLabel m (w+1) j
  let R := Function.update B.R (bank 10) (matrixWords prime H (mat false))
  have keep (k : Fin 18) (hk : k ≠ 10) : R (bank k) = B.R (bank k) := Function.update_of_ne (bank.injective.ne hk) _ _
  have keepRec (i) : R (r i) = S.R (r i) := (Function.update_of_ne (br 10 i).symm _ _).trans (kr i)
  have keepFrame (k i) : R (frame pool k i) = S.R (frame pool k i) :=
    (Function.update_of_ne (bp 10 _).symm _ _).trans (kf k i)
  have keepClock (i) : R (counters i) = S.R (counters i) :=
    (Function.update_of_ne (QueueLayout.block_ne _ _ host (by decide) (10 : Fin 18) i).symm _ _).trans (kc i)
  have matrices (k : Bool) : ∃ suffix, R (inputs (if id k then 7 else 2)) = matrixWords prime H (mat k) ++ suffix := by
    cases k
    · exact ⟨[],by simp [R,inputs,QueueLayout.formulaInputs]⟩
    · change ∃ suffix, R (bank 16) = matrixWords prime H projector ++ suffix
      rwa [keep 16 (by decide), kb 16 (by decide) (by decide)]
  have leaves := sourcePorts_ready inputs id mat H R matrices ((congrArg List.length (keep 8 (by decide))).trans ((congrArg List.length (kb 8 (by decide) (by decide))).trans bitWidth))
    ((keep 9 (by decide)).trans ((kb 9 (by decide) (by decide)).trans zeroWord)) ((keep 17 (by decide)).trans ((kb 17 (by decide) (by decide)).trans inputOne)) (fun i hi => by
      revert hi
      fin_cases i <;> simp <;> exact (keep _ (by decide)).trans (protectedScratch _ (by decide)))
  have run := physicalConjugation_writes body w j mat false true rfl h r clock count copyPorts (fun i => rc i 1) (rc 14 0).symm
    H hm pool source (fun a i j => bp _ j) (QueueLayout.normalizationPorts.trans r) (fun k => (rp 14 k).symm) (fun _ _ => br _ 14) (fun k => (rp 0 k).symm) (fun _ _ => br _ 0)
    (fun j => r.injective.ne ((by decide : ∀ j, QueueLayout.normalizationPorts j ≠ 14) j)) rfl (fun k j _ => (rp _ k).symm) (bank 10) (br 10 13)
    (QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans bank)) (QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans bank)) rfl
    (fun i j => (show ∀ i j, QueueLayout.readPorts i ≠ QueueLayout.digitPorts j ∨ i = 3 ∧ j = 0 by decide) i j |>.imp (fun h => (QueueLayout.directoryWork.trans bank).injective.ne h) id)
    (bank 12) (bank 9) (by change [bank 12,bank 0,bank 6].Nodup; simp) (by simp)
    (bank.injective.ne (by decide)) (fun i => bank.injective.ne (by revert i; decide))
    (fun i => bank.injective.ne (by revert i; decide)) (fun i => bank.injective.ne (by revert i; decide)) (ancestor j) rest (fun a i j _ => br _ _)
    fits detFits
  have separateOut : r 13 ≠ archive := by
    intro h
    have eq := congrArg Fin.val (host.injective h)
    change 18+13 = 36+2*m at eq
    omega
  have finish := residualWord_writes body weights (r 13) (scan 4) separateOut (fun _ _ => rfl) (fun _ _ => rfl) e
    projector (physicalLabel m (w+1) j) α α' H hm _ _ _ run u B
    ⟨⟨⟨by simpa [scan,QueueLayout.scanPorts,QueueLayout.readPorts,LabelDirectory.entry,List.append_assoc] using headEq,
      prefixLen,digitWidth,fun i hi => protectedScratch _ ((by decide : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i →
        QueueLayout.directoryWork (QueueLayout.readPorts i) ∈ ([0,3,4,5,6,7,11,14,15] : List (Fin 18))) i hi),(congrArg List.length (kb 8 (by decide) (by decide))).trans bitWidth,
      fun i hi => protectedScratch _ ((by decide : ∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 →
        QueueLayout.directoryWork (QueueLayout.digitPorts i) ∈ ([0,3,4,5,6,7,11,14,15] : List (Fin 18))) i hi),(kb 9 (by decide) (by decide)).trans zeroWord⟩,(kb 10 (by decide) (by decide)).trans packedBlank,
      (congrArg List.length (keepClock 0)).trans ticks,(keepClock 1).trans countBlank,(keepRec 14).trans pivot,
      (keepRec 15).trans oneWord,(keepRec 4).trans modulus,fun i hi hl => (keepRec i).trans (free i hi hl),
      fun k hk => (keepFrame k 2).trans (moduli k hk),fun k hk i hi => (keepFrame k i).trans (frames k hk i hi),
      leaves,(keepRec 4).trans modulus,(keepRec 12).trans (free 12 (by decide) (by decide)),
      fun k hk => (keepRec _).trans (free _ (scratchPort k hk).1 (scratchPort k hk).2)⟩,(kr 13).trans weightBank.1,by
        intro i j
        obtain ⟨row,col⟩ := weightBank.2 i j
        have weight (k : Fin 4) (hk : k = 1 ∨ k = 2) :
            B.R (coeff i j k) = S.R (coeff i j k) := by
          apply ws _ (apart _ 0) <;> intro eq <;> have v := congrArg Fin.val (host.injective eq) <;>
            rcases hk with rfl | rfl <;> simp [coefficientSlots] at v <;> omega
        refine ⟨?_,?_,(weight 1 (Or.inl rfl)).trans row,(weight 2 (Or.inr rfl)).trans col,?_⟩
        · by_cases h : i = j
          · subst j
            simpa [weights,QueueLayout.residualPorts,QueueLayout.residualSlots,coeff,
              coefficientSlots,Matrix.cons_val,Matrix.one_apply,bank,QueueLayout.block] using (kb 17 (by decide) (by decide)).trans inputOne
          · simpa [weights,QueueLayout.residualPorts,QueueLayout.residualSlots,coeff,
              coefficientSlots,Matrix.cons_val,Matrix.one_apply,h,bank,QueueLayout.block] using (kb 9 (by decide) (by decide)).trans zeroWord
        · change B.R (r 4) = _
          exact (kr 4).trans modulus
        · intro k hk
          obtain ⟨l,hl,hlt,slot⟩ := QueueLayout.residualScratch k hk
          have port : weights i j k = r l := congrArg (Sum.elim r (coeff i j)) slot
          rw [port]
          exact (kr l).trans (free l hl hlt)⟩
  simpa only [word,price,livePrice,liveRecordCost,← widths j hj,h,ite_true,live,conjugate] using finish

/-- Copy the directory before generating its residual matrices, so the classified scan can consume the original. -/
theorem physicalResidualQueue_copy_exec (body : P → Pr P T Q prime U)
    (w records : ℕ)
    (projector : Matrix (Fin m) (Fin m) (ZMod (prime^(w+1))))
    (H : ℕ) (hm : prime^(w+1) < 2^H) (registers : Fin ((36+2*m+1+(conjugationDepth m+1)*13)+3) ↪ Fin T) :
    let size := 36+2*m+1+(conjugationDepth m+1)*13
    let host := QueueLayout.block (n := size) 0 (by dsimp [size]; omega) registers
    let control := QueueLayout.block (n := 3) size (Nat.le_refl _) registers
    let mask := control 0
    let seed := control 1
    let tmp := control 2
    let bank := QueueLayout.block (n := 18) 0 (by omega) host
    let r := QueueLayout.block (n := 16) 18 (by omega) host
    let counters := QueueLayout.block (n := 2) 34 (by omega) host
    let clock := counters 0
    let count := counters 1
    let pool := QueueLayout.block (n := (conjugationDepth m+1)*13) (36+2*m+1) (by omega) host
    let coeff := fun i j : Fin m => (coefficientSlots i j).trans host
    let archive := host ⟨36+2*m, by omega⟩
    have archiveOff : ∀ i, bank (QueueLayout.directoryWork i) ≠ archive := fun i h => by
      have eq := congrArg Fin.val (host.injective h)
      change 0 + i.val = 36+2*m at eq
      omega
    have coeffOff : ∀ i j k l, r k ≠ coeff i j l := fun i j k l h => by
      have eq := congrArg Fin.val (host.injective h)
      change 18+k.val = (coefficientSlots (extra := (conjugationDepth m+1)*13) i j l).val at eq
      fin_cases l <;> simp [coefficientSlots, Matrix.cons_val] at eq <;> (try split_ifs at *) <;> omega
    ∀ (ancestor : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    {d : ℕ} (e : (Fin m ⊕ Fin m) ≃ Fin d)
    (α α' : Fin m → ZMod (prime^(w+1))),
    let padWord := matrixWords prime H (1 : Matrix (Fin d) (Fin d) (ZMod (prime^(w+1))))
    ∀ (source : Fin T) (v : HS T Q prime U) (B : Stacks T prime),
    let S := {B with R := Function.update B.R (bank 2) (B.R source)}
    ∀ (_apart : [source,bank 2,bank 4,tmp].Nodup) (_maskOff : source ≠ mask) (_archiveOff : source ≠ archive)
    (_free : B.R (bank 2) = []) (_scratch : B.R (bank 4) = []) (_tmp : B.R tmp = [])
    (_seedWord : S.R seed = padWord)
    (_weightBank : S.R (r 13) = [] ∧ ∀ i j, let s := coeff i j
      S.R (s 1) = binSyms H (α i).val ∧ S.R (s 2) = binSyms H (α' j).val)
    (_ready :
      (∀ i : Fin 18, i ∈ [0,3,4,5,6,7,11,14,15] → S.R (bank i) = []) ∧ (S.R (bank 8)).length = H ∧
      S.R (bank 9) = binSyms H 0 ∧ S.R (bank 10) = [] ∧
       (S.R clock).length = w ∧ S.R count = [] ∧ S.R (r 14) = [] ∧
      S.R (r 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ S.R (r 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → S.R (r i) = []) ∧
      (∀ k ≤ conjugationDepth m, S.R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ conjugationDepth m, ∀ i : Fin 13, i ≠ 2 → S.R (frame pool k i) = []) ∧
      (∃ suffix, S.R (bank 16) = matrixWords prime H projector ++ suffix) ∧
      S.R (bank 17) = binSyms H (1 : ZMod (prime^(w+1))).val)
    (_widths : ∀ j < records, (S.R (bank 12)).length = (ancestor j).length)
    (_width : (S.R (bank 1)).length = w+1) (_empty : S.R (archive) = [])
    (_directory : B.R source = (List.range records).flatMap (LabelDirectory.entry ancestor m (w+1)) ++ tail)
    (_output : S.R (bank 13) = []) (_bits : S.R mask = (List.range records).map fun j => bitSymbol (LabelStock.live m (w+1) 1 j)),
    let inputs := QueueLayout.formulaInputs.trans bank
    let formula := sourcePorts (m := m) inputs id
    let weights := fun i j => QueueLayout.residualPorts r (coeff i j) (coeffOff i j)
    let scan := QueueLayout.scanPorts (QueueLayout.directoryWork.trans bank) archive archiveOff
    let num := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    let f := determinant (matrixInput false)
    let conjugate : Pr P T Q prime U := (.seq (directoryMatrix m (QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans bank)) (QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans bank)) (bank 12) (bank 9) (bank 10)) (.seq (.seq (.seq (compile (readLeaf (leafBank formula)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse prime r clock count))
        (.seq (packedConjugate pool formula (QueueLayout.normalizationPorts.trans r) false true) (.seq (bclear (r 0)) (bclear (r 14))))) (bclear (bank 10))))
    let live : Pr P T Q prime U := .seq conjugate (.seq (sequence (fun i => sequence
      (fun j => blockEntry weights (e.symm i) (e.symm j)) (List.finRange d)) (List.finRange d)) (bclear (r 13)))
    let active := LabelStock.live m (w+1) 1
    let word := fun j => if active j then matrixWords prime H (projectorResidual e projector α α' (physicalLabel m (w+1) j)) else padWord
    let livePrice := liveRecordCost m d w H (S.R (bank 12)).length cost (time H (readTime H) f)
    let branch := fun p => Prog.seq p (.seq (moveR (scan 4) (scan 5) id) (advanceDirectory m scan))
    let words := (List.range records).flatMap word
    let generate := (.seq (maskedScan mask (branch live) (branch (bcopy seed (scan 4) (scan 3) tmp)))
      (moveR (scan 5) (scan 4) id) : Pr P T Q prime U)
    let D := queueResult S mask (scan 2) (scan 4) tail words
    ∃ z n, z.user = v.user ∧ D.R source = B.R source ∧ D.R archive = words ∧
      n ≤ 6*(B.R source).length+6 + ((List.range records).countP active * (livePrice + 4*(d*d*H)) +
        (List.range records).countP (fun j => !active j) * (10*(d*d*H)+6) +
        records * (4*(S.R (bank 12)).length+4+(m*m*(4*(w+1)+4)+1)+6) + 4) ∧
      Exec body ((bcopy source (bank 2) (bank 4) tmp).seq generate) (mk v B) n (mk z D) := by
  intro size host control mask seed tmp bank r counters clock count pool coeff archive archiveOff coeffOff ancestor tail
    d e α α' padWord source v B S apart maskOff sourceOff free scratch tmpFree seedWord weightBank ready
    widths width empty directory output bits inputs formula weights scan num cost f conjugate live active word
    livePrice branch words generate D
  obtain ⟨u,user,copy⟩ := bcopy_exec body apart v B scratch tmpFree
  rw [free,List.append_nil] at copy
  have tmpBlank : S.R tmp = [] := (Function.update_of_ne (by
    intro eq; exact (List.nodup_cons.mp apart.tail).1 (by simp [eq])) _ _).trans tmpFree
  have blank : S.R (bank 4) = [] := (Function.update_of_ne (bank.injective.ne (by decide)) _ _).trans scratch
  have stored : S.R (bank 2) = B.R source := Function.update_self ..
  obtain ⟨_,z,n,returned,time,run⟩ := physicalResidualQueue_exec body w records projector H hm registers
    ancestor tail e α α' u S seedWord tmpBlank weightBank ready widths width blank empty (stored.trans directory) output bits
  have separate : source ≠ bank 2 := by
    intro eq
    exact (List.nodup_cons.mp apart).1 (eq ▸ List.mem_cons_self)
  refine ⟨z,_,returned.trans user,?_,Function.update_self ..,Nat.add_le_add_left time _,Exec.seq copy run⟩
  change Function.update (Function.update (Function.update S.R mask []) (bank 2) tail) archive words source = _
  simp [Function.update_of_ne,sourceOff,separate,maskOff,S]

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
