module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalConjugation
public import IntegerMultBounds.MathlibTM2.Cover.FallbackQueueLayout
public import IntegerMultBounds.MathlibTM2.Cover.FallbackResidualWord

/-! Generate weighted residual matrices in physical directory order.
The conjugate-only queue can be restored from commit 2c23aa3c. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι P U : Type} {T Q m D : ℕ}

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem physicalResidualQueue_exec (body : P → Pr P T Q prime U)
    (w records : ℕ)
    (mat : ℕ → ι → Matrix (Fin m) (Fin m) (ZMod (prime^(w+1)))) (b proj : ι) (label : ∀ j, mat j b = physicalLabel m (w+1) j)
    (r : Fin 16 ↪ Fin T) (clock count : Fin T) (copyPorts : [clock,count,r 2,r 3].Nodup)
    (outside : ∀ i, r i ≠ count) (clockPivot : clock ≠ r 14)
    (H : ℕ) (hm : prime^(w+1) < 2^H)
    (pool : Fin ((D+1)*13) ↪ Fin T) (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T)
    (apart : ∀ a i j, source a i ≠ pool j) (q : Fin 14 ↪ Fin T)
    (poolPivot : ∀ k, pool k ≠ r 14) (srcPivot : ∀ a i, source a i ≠ r 14)
    (poolInv : ∀ k, pool k ≠ r 0) (srcInv : ∀ a i, source a i ≠ r 0)
    (qPivot : ∀ j, q j ≠ r 14) (shared : q 0 = r 0)
    (poolFree : ∀ k j, j = 1 ∨ j = 13 → pool k ≠ q j)
    (work : Fin 16 ↪ Fin T) (archive : Fin T) (archiveOff : ∀ i, work i ≠ archive)
    (distinct : work 10 ≠ q 3)
    (ancestor : ℕ → List (Fin (prime+4))) (tail padWord : List (Fin (prime+4)))
    (srcFree : ∀ a i j, j = 1 ∨ j = 13 → source a i ≠ q j)
    (mask seed tmp : Fin T)
    (maskOff : ∀ k, mask ≠ QueueLayout.scanPorts work archive archiveOff k)
    (separateOut : q 3 ≠ archive) (padPorts : [seed,archive,work 4,tmp].Nodup)
    {d : ℕ} (e : (Fin m ⊕ Fin m) ≃ Fin d) (weights : Fin m → Fin m → Fin 17 ↪ Fin T)
    (inputPort : ∀ i j, weights i j 13 = q 3) (outputPort : ∀ i j, weights i j 16 = archive)
    (α α' : Fin m → ZMod (prime^(w+1)))
    (workspace : Regs T prime → Prop)
    (stable : ∀ R M, workspace R → (∀ k, k ≠ mask → k ≠ work 2 → k ≠ work 13 → M k = R k) → workspace M)
    (padReady : ∀ R, workspace R → R seed = padWord ∧ R (work 4) = [] ∧ R tmp = [])
    (weightBank : ∀ R, workspace R → R (q 3) = [] ∧ ∀ i j, let s := weights i j
      R (s 0) = binSyms H ((1 : Matrix (Fin m) (Fin m) (ZMod (prime^(w+1)))) i j).val ∧
      R (s 2) = binSyms H (prime^(w+1)) ∧ R (s 14) = binSyms H (α i).val ∧ R (s 15) = binSyms H (α' j).val ∧
      ∀ k : Fin 17, k = 1 ∨ 3 ≤ k ∧ k ≤ 12 → R (s k) = [])
    (ready : ∀ j < records, LabelStock.live m (w+1) 1 j = true → ∀ S, workspace S →
      (S (work 12)).length = (ancestor j).length ∧ (S (work 1)).length = w+1 ∧
      (∀ i : Fin 16, i ∈ [0,3,4,5,6,7,11,14,15] → S (work i) = []) ∧ (S (work 8)).length = H ∧
      S (work 9) = binSyms H 0 ∧ S (work 10) = [] ∧
      (let R := Function.update S (work 10) (matrixWords prime H (mat j b))
       (R clock).length = w ∧ R count = [] ∧ R (r 14) = [] ∧
      R (r 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ R (r 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → R (r i) = []) ∧
      (∀ k ≤ D, R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame pool k i) = []) ∧
      (∀ a, leafReady (fun c _ => source c) (mat j) H a (source a 3) R) ∧
      R (q 2) = binSyms H (prime^(w+1)) ∧ R (q 13) = [] ∧
      ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (q k) = []))
    (v : HS T Q prime U) (S : Stacks T prime) (start : workspace S.R)
    (widths : ∀ j < records, (S.R (work 12)).length = (ancestor j).length)
    (width : (S.R (work 1)).length = w+1) (blank : S.R (work 4) = []) (empty : S.R (archive) = [])
    (directory : S.R (work 2) = (List.range records).flatMap (LabelDirectory.entry ancestor m (w+1)) ++ tail)
    (output : S.R (work 13) = []) (bits : S.R mask = (List.range records).map fun j => bitSymbol (LabelStock.live m (w+1) 1 j)) :
    let scan := QueueLayout.scanPorts work archive archiveOff
    let num := fun i j : Fin m => numerator (matrixInput b) (matrixInput proj) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    (∀ i j, (num i j).depth ≤ D) →
    let f := determinant (matrixInput b)
    f.depth ≤ D →
    let C := 48*H*H+152*H+66
    let conjugate : Pr P T Q prime U := (.seq (directoryMatrix m (QueueLayout.readPorts.trans work) (QueueLayout.digitPorts.trans work) (work 12) (work 9) (work 10)) (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse prime r clock count))
        (.seq (packedConjugate pool source q b proj) (.seq (bclear (r 0)) (bclear (r 14))))) (bclear (work 10))))
    let live : Pr P T Q prime U := .seq conjugate (.seq (sequence (fun i => sequence
      (fun j => blockEntry weights (e.symm i) (e.symm j)) (List.finRange d)) (List.finRange d)) (bclear (q 3)))
    let active := LabelStock.live m (w+1) 1
    let word := fun j => if active j then matrixWords prime H (projectorResidual e (mat j proj) α α' (mat j b)) else padWord
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
  intro scan num cost fits f detFits C conjugate live active word price
  apply directoryQueue_exec body scan mask maskOff m (w+1) records active live seed tmp padPorts padWord price
    ancestor word tail workspace stable padReady (fun j _ h => by simp [word,price,h])
    _ v S start widths width blank empty directory output bits
  intro j hj h u B ⟨ws,rest,headEq⟩
  have ⟨prefixLen,digitWidth,scratch,bitWidth,zeroWord,packedBlank,arith⟩ := ready j hj h B.R ws
  have run := physicalConjugation_writes body w j (mat j) b proj (label j) h r clock count copyPorts outside clockPivot
    H hm pool source apart q poolPivot srcPivot poolInv srcInv qPivot shared poolFree (work 10) distinct
    (QueueLayout.readPorts.trans work) (QueueLayout.digitPorts.trans work) rfl
    (fun i j => (show ∀ i j, QueueLayout.readPorts i ≠ QueueLayout.digitPorts j ∨ i = 3 ∧ j = 0 by decide) i j |>.imp (fun h => work.injective.ne h) id)
    (work 12) (work 9) (by change [work 12,work 0,work 6].Nodup; simp) (by simp)
    (work.injective.ne (by decide)) (fun i => work.injective.ne (by revert i; decide))
    (fun i => work.injective.ne (by revert i; decide)) (fun i => work.injective.ne (by revert i; decide)) (ancestor j) rest srcFree
    fits detFits
  have finish := residualWord_writes body weights (q 3) (scan 4) separateOut inputPort outputPort e
    (mat j proj) (mat j b) α α' H hm _ _ _ run u B
    ⟨⟨⟨by simpa [scan,QueueLayout.scanPorts,QueueLayout.readPorts,LabelDirectory.entry,List.append_assoc] using headEq,
      prefixLen,digitWidth,fun i hi => scratch _ ((by decide : ∀ i : Fin 7, i = 0 ∨ 3 ≤ i →
        QueueLayout.readPorts i ∈ ([0,3,4,5,6,7,11,14,15] : List (Fin 16))) i hi),bitWidth,
      fun i hi => scratch _ ((by decide : ∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 →
        QueueLayout.digitPorts i ∈ ([0,3,4,5,6,7,11,14,15] : List (Fin 16))) i hi),zeroWord⟩,packedBlank,arith⟩,weightBank B.R ws⟩
  simpa only [word,price,h,ite_true,live,conjugate] using finish

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
