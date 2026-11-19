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

theorem physicalResidualQueue_exec (body : P → Pr P T Q prime U)
    (w records : ℕ)
    (projector : Matrix (Fin m) (Fin m) (ZMod (prime^(w+1))))
    (H : ℕ) (hm : prime^(w+1) < 2^H) (host : Fin (36+(conjugationDepth m+1)*13) ↪ Fin T) :
    let bank := QueueLayout.block (n := 18) 0 (by omega) host
    let r := QueueLayout.block (n := 16) 18 (by omega) host
    let counters := QueueLayout.block (n := 2) 34 (by omega) host
    let clock := counters 0
    let count := counters 1
    let pool := QueueLayout.block (n := (conjugationDepth m+1)*13) 36 (by omega) host
    ∀ (archive : Fin T) (archiveOff : ∀ i, bank (QueueLayout.directoryWork i) ≠ archive)
    (ancestor : ℕ → List (Fin (prime+4))) (tail padWord : List (Fin (prime+4)))
    (mask seed tmp : Fin T)
    (maskOff : ∀ k, mask ≠ QueueLayout.scanPorts (QueueLayout.directoryWork.trans bank) archive archiveOff k)
    (separateOut : r 13 ≠ archive) (padPorts : [seed,archive,bank 4,tmp].Nodup)
    {d : ℕ} (e : (Fin m ⊕ Fin m) ≃ Fin d) (coeff : Fin m → Fin m → Fin 4 ↪ Fin T)
    (coeffOff : ∀ i j k l, r k ≠ coeff i j l) (outputPort : ∀ i j, coeff i j 3 = archive)
    (α α' : Fin m → ZMod (prime^(w+1)))
    (workspace : Regs T prime → Prop)
    (stable : ∀ R M, workspace R → (∀ k, k ≠ mask → k ≠ bank 2 → k ≠ bank 13 → M k = R k) → workspace M)
    (padReady : ∀ R, workspace R → R seed = padWord ∧ R (bank 4) = [] ∧ R tmp = [])
    (weightBank : ∀ R, workspace R → R (r 13) = [] ∧ ∀ i j, let s := coeff i j
      R (s 0) = binSyms H ((1 : Matrix (Fin m) (Fin m) (ZMod (prime^(w+1)))) i j).val ∧
      R (s 1) = binSyms H (α i).val ∧ R (s 2) = binSyms H (α' j).val)
    (ready : ∀ j < records, LabelStock.live m (w+1) 1 j = true → ∀ S, workspace S →
      (S (bank 12)).length = (ancestor j).length ∧ (S (bank 1)).length = w+1 ∧
      (∀ i : Fin 18, i ∈ [0,3,4,5,6,7,11,14,15] → S (bank i) = []) ∧ (S (bank 8)).length = H ∧
      S (bank 9) = binSyms H 0 ∧ S (bank 10) = [] ∧
       (S clock).length = w ∧ S count = [] ∧ S (r 14) = [] ∧
      S (r 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ S (r 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → S (r i) = []) ∧
      (∀ k ≤ conjugationDepth m, S (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ conjugationDepth m, ∀ i : Fin 13, i ≠ 2 → S (frame pool k i) = []) ∧
      (∃ suffix, S (bank 16) = matrixWords prime H projector ++ suffix) ∧
      S (bank 17) = binSyms H (1 : ZMod (prime^(w+1))).val)
    (v : HS T Q prime U) (S : Stacks T prime) (start : workspace S.R)
    (widths : ∀ j < records, (S.R (bank 12)).length = (ancestor j).length)
    (width : (S.R (bank 1)).length = w+1) (blank : S.R (bank 4) = []) (empty : S.R (archive) = [])
    (directory : S.R (bank 2) = (List.range records).flatMap (LabelDirectory.entry ancestor m (w+1)) ++ tail)
    (output : S.R (bank 13) = []) (bits : S.R mask = (List.range records).map fun j => bitSymbol (LabelStock.live m (w+1) 1 j)),
    let inputs := QueueLayout.formulaInputs.trans bank
    let source := sourcePorts (m := m) inputs id
    let weights := fun i j => QueueLayout.residualPorts r (coeff i j) (coeffOff i j)
    let scan := QueueLayout.scanPorts (QueueLayout.directoryWork.trans bank) archive archiveOff
    let num := fun i j : Fin m => numerator (matrixInput false) (matrixInput true) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    let f := determinant (matrixInput false)
    let C := 48*H*H+152*H+66
    let conjugate : Pr P T Q prime U := (.seq (directoryMatrix m (QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans bank)) (QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans bank)) (bank 12) (bank 9) (bank 10)) (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse prime r clock count))
        (.seq (packedConjugate pool source (QueueLayout.normalizationPorts.trans r) false true) (.seq (bclear (r 0)) (bclear (r 14))))) (bclear (bank 10))))
    let live : Pr P T Q prime U := .seq conjugate (.seq (sequence (fun i => sequence
      (fun j => blockEntry weights (e.symm i) (e.symm j)) (List.finRange d)) (List.finRange d)) (bclear (r 13)))
    let active := LabelStock.live m (w+1) 1
    let word := fun j => if active j then matrixWords prime H (projectorResidual e projector α α' (physicalLabel m (w+1) j)) else padWord
    let price := fun j => if active j then ((m*(m*(12*(ancestor j).length+8*((w+1)*(m*m))+(w+1)*(7*H+prime+31)+10*H+42)+1)+1) + (time H (readTime H) f + (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) +
       ((m*(m*(cost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) + (2*(m*m*H)+2)) +
       (d*(d*(8*(m*m*H)+96*H*H+344*H+182)+1)+1)+(2*(m*m*H)+2) else 6*padWord.length+6
    let branch := fun p => Prog.seq p (.seq (moveR (scan 4) (scan 5) id) (advanceDirectory m scan))
    let words := (List.range records).flatMap word
    ∃ z F n, z.user = v.user ∧ F.R mask = [] ∧ F.R (scan 2) = tail ∧ F.R (scan 4) = words ∧
      F.R (scan 5) = [] ∧ (∀ k, k ≠ mask → k ≠ scan 2 → k ≠ scan 4 → F.R k = S.R k) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      n ≤ ((List.range records).map fun j => price j+2*(word j).length+2+
        (4*(ancestor j).length+4+(m*m*(4*(w+1)+4)+1))+4).sum+2+(2*words.length+2) ∧
      Exec body (.seq (maskedScan mask (branch live) (branch (bcopy seed (scan 4) (scan 3) tmp)))
        (moveR (scan 5) (scan 4) id)) (mk v S) n (mk z F) := by
  intro bank r counters clock count pool archive archiveOff ancestor tail padWord mask seed tmp maskOff separateOut
    padPorts d e coeff coeffOff outputPort α α' workspace stable padReady weightBank ready v S start
    widths width blank empty directory output bits
  have br (i j) : bank i ≠ r j := QueueLayout.block_ne _ _ host (by decide) i j
  have bp (i j) : bank i ≠ pool j := QueueLayout.block_ne _ _ host (by decide) i j
  have rp (i j) : r i ≠ pool j := QueueLayout.block_ne _ _ host (by decide) i j
  have rc (i j) : r i ≠ counters j := QueueLayout.block_ne _ _ host (by decide) i j
  have copyPorts : [clock,count,r 2,r 3].Nodup := by
    simp [clock,count,counters.injective.eq_iff,(rc _ _).symm,r.injective.eq_iff]
  intro inputs source weights scan num cost f C conjugate live active word price
  have detFits : f.depth ≤ conjugationDepth m := Nat.le_max_left _ _
  have fits (i j : Fin m) : (num i j).depth ≤ conjugationDepth m :=
    le_trans (Finset.le_sup (f := fun ij : Fin m × Fin m => (num ij.1 ij.2).depth)
      (Finset.mem_univ (i,j))) (Nat.le_max_right _ _)
  apply directoryQueue_exec body scan mask maskOff m (w+1) records active live seed tmp padPorts padWord price
    ancestor word tail workspace stable padReady (fun j _ h => by simp [word,price,h])
    _ v S start widths width blank empty directory output bits
  intro j hj h u B ⟨ws,rest,headEq⟩
  obtain ⟨prefixLen,digitWidth,scratch,bitWidth,zeroWord,packedBlank,ticks,countBlank,pivot,oneWord,modulus,free,moduli,frames,projTape,inputOne⟩ := ready j hj h B.R ws
  have scratchPort : ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 →
      QueueLayout.normalizationPorts k ≠ 4 ∧ QueueLayout.normalizationPorts k < 13 := by decide
  let mat : Bool → Matrix (Fin m) (Fin m) (ZMod (prime^(w+1))) := fun k => if k then projector else physicalLabel m (w+1) j
  let R := Function.update B.R (bank 10) (matrixWords prime H (mat false))
  have keep (k : Fin 18) (hk : k ≠ 10) : R (bank k) = B.R (bank k) := Function.update_of_ne (bank.injective.ne hk) _ _
  have keepRec (i) : R (r i) = B.R (r i) := Function.update_of_ne (br 10 i).symm _ _
  have keepFrame (k i) : R (frame pool k i) = B.R (frame pool k i) := Function.update_of_ne (bp 10 _).symm _ _
  have keepClock (i) : R (counters i) = B.R (counters i) :=
    Function.update_of_ne (QueueLayout.block_ne _ _ host (by decide) (10 : Fin 18) i).symm _ _
  have matrices (k : Bool) : ∃ suffix, R (inputs (if id k then 7 else 2)) = matrixWords prime H (mat k) ++ suffix := by
    cases k
    · exact ⟨[],by simp [R,inputs,QueueLayout.formulaInputs]⟩
    · change ∃ suffix, R (bank 16) = matrixWords prime H projector ++ suffix
      rwa [keep 16 (by decide)]
  have leaves := sourcePorts_ready inputs id mat H R matrices ((congrArg List.length (keep 8 (by decide))).trans bitWidth)
    ((keep 9 (by decide)).trans zeroWord) ((keep 17 (by decide)).trans inputOne) (fun i hi => by
      revert hi
      fin_cases i <;> simp <;> exact (keep _ (by decide)).trans (scratch _ (by decide)))
  have run := physicalConjugation_writes body w j mat false true rfl h r clock count copyPorts (fun i => rc i 1) (rc 14 0).symm
    H hm pool source (fun a i j => bp _ j) (QueueLayout.normalizationPorts.trans r) (fun k => (rp 14 k).symm) (fun _ _ => br _ 14) (fun k => (rp 0 k).symm) (fun _ _ => br _ 0)
    (fun j => r.injective.ne ((by decide : ∀ j, QueueLayout.normalizationPorts j ≠ 14) j)) rfl (fun k j _ => (rp _ k).symm) (bank 10) (br 10 13)
    (QueueLayout.readPorts.trans (QueueLayout.directoryWork.trans bank)) (QueueLayout.digitPorts.trans (QueueLayout.directoryWork.trans bank)) rfl
    (fun i j => (show ∀ i j, QueueLayout.readPorts i ≠ QueueLayout.digitPorts j ∨ i = 3 ∧ j = 0 by decide) i j |>.imp (fun h => (QueueLayout.directoryWork.trans bank).injective.ne h) id)
    (bank 12) (bank 9) (by change [bank 12,bank 0,bank 6].Nodup; simp) (by simp)
    (bank.injective.ne (by decide)) (fun i => bank.injective.ne (by revert i; decide))
    (fun i => bank.injective.ne (by revert i; decide)) (fun i => bank.injective.ne (by revert i; decide)) (ancestor j) rest (fun a i j _ => br _ _)
    fits detFits
  have finish := residualWord_writes body weights (r 13) (scan 4) separateOut (fun _ _ => rfl) outputPort e
    projector (physicalLabel m (w+1) j) α α' H hm _ _ _ run u B
    ⟨⟨⟨by simpa [scan,QueueLayout.scanPorts,QueueLayout.readPorts,LabelDirectory.entry,List.append_assoc] using headEq,
      prefixLen,digitWidth,fun i hi => scratch _ ((by decide : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i →
        QueueLayout.directoryWork (QueueLayout.readPorts i) ∈ ([0,3,4,5,6,7,11,14,15] : List (Fin 18))) i hi),bitWidth,
      fun i hi => scratch _ ((by decide : ∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 →
        QueueLayout.directoryWork (QueueLayout.digitPorts i) ∈ ([0,3,4,5,6,7,11,14,15] : List (Fin 18))) i hi),zeroWord⟩,packedBlank,
      (congrArg List.length (keepClock 0)).trans ticks,(keepClock 1).trans countBlank,(keepRec 14).trans pivot,
      (keepRec 15).trans oneWord,(keepRec 4).trans modulus,fun i hi hl => (keepRec i).trans (free i hi hl),
      fun k hk => (keepFrame k 2).trans (moduli k hk),fun k hk i hi => (keepFrame k i).trans (frames k hk i hi),
      leaves,(keepRec 4).trans modulus,(keepRec 12).trans (free 12 (by decide) (by decide)),
      fun k hk => (keepRec _).trans (free _ (scratchPort k hk).1 (scratchPort k hk).2)⟩,(weightBank B.R ws).1,by
        intro i j
        obtain ⟨identity,row,col⟩ := (weightBank B.R ws).2 i j
        refine ⟨identity,?_,row,col,?_⟩
        · change B.R (r 4) = _
          exact modulus
        · intro k hk
          obtain ⟨l,hl,hlt,slot⟩ := QueueLayout.residualScratch k hk
          have port : weights i j k = r l := congrArg (Sum.elim r (coeff i j)) slot
          rw [port]
          exact free l hl hlt⟩
  simpa only [word,price,h,ite_true,live,conjugate] using finish

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
