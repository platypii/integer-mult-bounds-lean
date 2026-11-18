module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalConjugation
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryScan

/-! Generate the conjugated matrices for a physical directory in record order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι P U : Type} {T Q m D : ℕ}

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem physicalConjugationQueue_exec (body : P → Pr P T Q prime U)
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
    (packed : Fin T) (distinct : packed ≠ q 3) (a : Fin 7 ↪ Fin T) (digits : Fin 6 ↪ Fin T)
    (digitPort : a 3 = digits 0) (sep : ∀ i j, a i ≠ digits j ∨ i = 3 ∧ j = 0)
    (prefixWidth zeros : Fin T) (ports : [prefixWidth,a 0,a 6].Nodup)
    (external : [prefixWidth,zeros,packed].Nodup) (prefixAcc : prefixWidth ≠ digits 2)
    (aOut : ∀ i, a i ≠ packed) (bOut : ∀ i, digits i ≠ packed) (zeroPort : ∀ i, zeros ≠ digits i)
    (ancestor : ℕ → List (Fin (prime+4))) (tail padWord : List (Fin (prime+4)))
    (srcFree : ∀ a i j, j = 1 ∨ j = 13 → source a i ≠ q j)
    (scan : Fin 6 ↪ Fin T) (mask seed tmp : Fin T) (maskOff : ∀ k, mask ≠ scan k)
    (queueIn : scan 2 = a 2) (queueOut : scan 4 = q 3) (padPorts : [seed,scan 4,scan 3,tmp].Nodup)
    (workspace : Regs T prime → Prop)
    (stable : ∀ R M, workspace R → (∀ k, k ≠ mask → k ≠ scan 2 → k ≠ scan 5 → M k = R k) → workspace M)
    (padReady : ∀ R, workspace R → R seed = padWord ∧ R (scan 3) = [] ∧ R tmp = [])
    (ready : ∀ j < records, LabelStock.live m (w+1) 1 j = true → ∀ S, workspace S →
      (S prefixWidth).length = (ancestor j).length ∧ (S (a 1)).length = w+1 ∧
      (∀ i : Fin 7, i = 0 ∨ 3 ≤ i → S (a i) = []) ∧ (S (digits 4)).length = H ∧
      (∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 → S (digits i) = []) ∧ S zeros = binSyms H 0 ∧ S packed = [] ∧
      (let R := Function.update S packed (matrixWords prime H (mat j b))
       (R clock).length = w ∧ R count = [] ∧ R (r 14) = [] ∧
      R (r 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ R (r 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → R (r i) = []) ∧
      (∀ k ≤ D, R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame pool k i) = []) ∧
      (∀ a, leafReady (fun c _ => source c) (mat j) H a (source a 3) R) ∧
      R (q 2) = binSyms H (prime^(w+1)) ∧ R (q 13) = [] ∧
      ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (q k) = []))
    (v : HS T Q prime U) (S : Stacks T prime) (start : workspace S.R)
    (widths : ∀ j < records, (S.R (scan 0)).length = (ancestor j).length)
    (width : (S.R (scan 1)).length = w+1) (blank : S.R (scan 3) = []) (empty : S.R (scan 4) = [])
    (directory : S.R (scan 2) = (List.range records).flatMap (LabelDirectory.entry ancestor m (w+1)) ++ tail)
    (output : S.R (scan 5) = []) (bits : S.R mask = (List.range records).map fun j => bitSymbol (LabelStock.live m (w+1) 1 j)) :
    let num := fun i j : Fin m => numerator (matrixInput b) (matrixInput proj) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    (∀ i j, (num i j).depth ≤ D) →
    let f := determinant (matrixInput b)
    f.depth ≤ D →
    let C := 48*H*H+152*H+66
    let live : Pr P T Q prime U := (.seq (directoryMatrix m a digits prefixWidth zeros packed) (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse prime r clock count))
        (.seq (packedConjugate pool source q b proj) (.seq (bclear (r 0)) (bclear (r 14))))) (bclear packed)))
    let active := LabelStock.live m (w+1) 1
    let word := fun j => if active j then matrixWords prime H (mat j b * mat j proj * (mat j b)⁻¹) else padWord
    let price := fun j => if active j then ((m*(m*(12*(ancestor j).length+8*((w+1)*(m*m))+(w+1)*(7*H+prime+31)+10*H+42)+1)+1) + (time H (readTime H) f + (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) +
       ((m*(m*(cost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) + (2*(m*m*H)+2)) else 6*padWord.length+6
    let branch := fun p => Prog.seq p (.seq (moveR (scan 4) (scan 5) id) (advanceDirectory m scan))
    let words := (List.range records).flatMap word
    ∃ z F n, z.user = v.user ∧ F.R mask = [] ∧ F.R (scan 2) = tail ∧ F.R (scan 4) = words ∧
      F.R (scan 5) = [] ∧ (∀ k, k ≠ mask → k ≠ scan 2 → k ≠ scan 4 → F.R k = S.R k) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      n ≤ ((List.range records).map fun j => price j+2*(word j).length+2+
        (4*(ancestor j).length+4+(m*m*(4*(w+1)+4)+1))+4).sum+2+(2*words.length+2) ∧
      Exec body (.seq (maskedScan mask (branch live) (branch (bcopy seed (scan 4) (scan 3) tmp)))
        (moveR (scan 5) (scan 4) id)) (mk v S) n (mk z F) := by
  intro num cost fits f detFits C live active word price
  apply directoryQueue_exec body scan mask maskOff m (w+1) records active live seed tmp padPorts padWord price
    ancestor word tail workspace stable padReady (fun j _ h => by simp [word,price,h])
    _ v S start widths width blank empty directory output bits
  intro j hj h u B ⟨ws,rest,headEq⟩
  have ⟨prefixLen,digitWidth,scratch,bitWidth,digitFree,zeroWord,packedBlank,arith⟩ := ready j hj h B.R ws
  have run := physicalConjugation_writes body w j (mat j) b proj (label j) h r clock count copyPorts outside clockPivot
    H hm pool source apart q poolPivot srcPivot poolInv srcInv qPivot shared poolFree packed distinct a digits
    digitPort sep prefixWidth zeros ports external prefixAcc aOut bOut zeroPort (ancestor j) rest srcFree
    fits detFits u B ⟨⟨by simpa [queueIn,LabelDirectory.entry,List.append_assoc] using headEq,
      prefixLen,digitWidth,scratch,bitWidth,digitFree,zeroWord⟩,packedBlank,arith⟩
  simpa only [word,price,h,ite_true,queueOut,live] using run

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
