module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugationRun
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDirectoryMatrix
import IntegerMultBounds.MathlibTM2.Cover.FallbackRewind

/-! Evaluate conjugation at a live physical label and release its packed tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι P U : Type} {T Q m D : ℕ}

open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem physicalConjugationFromReader_writes (body : P → Pr P T Q prime U)
    (w j : ℕ)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod (prime^(w+1)))) (b proj : ι) (label : mat b = physicalLabel m (w+1) j)
    (live : LabelStock.live m (w+1) 1 j = true)
    (r : Fin 16 ↪ Fin T) (clock count : Fin T) (copyPorts : [clock,count,r 2,r 3].Nodup)
    (outside : ∀ i, r i ≠ count) (clockPivot : clock ≠ r 14)
    (H : ℕ) (hm : prime^(w+1) < 2^H)
    (pool : Fin ((D+1)*13) ↪ Fin T) (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T)
    (apart : ∀ a i j, source a i ≠ pool j) (q : Fin 14 ↪ Fin T)
    (poolPivot : ∀ k, pool k ≠ r 14) (srcPivot : ∀ a i, source a i ≠ r 14)
    (poolInv : ∀ k, pool k ≠ r 0) (srcInv : ∀ a i, source a i ≠ r 0)
    (qPivot : ∀ j, q j ≠ r 14) (shared : q 0 = r 0)
    (poolFree : ∀ k j, j = 1 ∨ j = 13 → pool k ≠ q j)
    (packed : Fin T) (distinct : packed ≠ q 3)
    (ok : Regs T prime → Prop) (reader : Pr P T Q prime U) (readCost : ℕ)
    (readLabel : Writes body ok packed reader (matrixWords prime H (mat b)) readCost)
    (srcFree : ∀ a i j, j = 1 ∨ j = 13 → source a i ≠ q j) :
    let num := fun i j : Fin m => numerator (matrixInput b) (matrixInput proj) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    (∀ i j, (num i j).depth ≤ D) →
    let f := determinant (matrixInput b)
    f.depth ≤ D →
    let C := 48*H*H+152*H+66
    Writes body (fun S => ok S ∧ S packed = [] ∧
      (let R := Function.update S packed (matrixWords prime H (mat b))
       (R clock).length = w ∧ R count = [] ∧ R (r 14) = [] ∧
      R (r 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ R (r 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → R (r i) = []) ∧
      (∀ k ≤ D, R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame pool k i) = []) ∧
      (∀ a, leafReady (fun c _ => source c) mat H a (source a 3) R) ∧
      R (q 2) = binSyms H (prime^(w+1)) ∧ R (q 13) = [] ∧
      ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (q k) = [])) (q 3)
      (.seq reader (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse prime r clock count))
        (.seq (packedConjugate pool source q b proj) (.seq (bclear (r 0)) (bclear (r 14))))) (bclear packed)))
      (matrixWords prime H (mat b * mat proj * (mat b)⁻¹))
      (readCost + (time H (readTime H) f + (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) +
       ((m*(m*(cost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) + (2*(m*m*H)+2))
 := by
  intro num cost fits f detFits C v S ⟨prepared,blank,ready⟩
  obtain ⟨u,n,hu,hn,read⟩ := readLabel v S prepared
  rw [blank,List.append_nil] at read
  let B := {S with R := Function.update S.R packed (matrixWords prime H (mat b))}
  have unit := (Matrix.isUnit_iff_isUnit_det _).mp ((physicalLabel_live (by omega) j).mp live)
  rw [← label] at unit
  obtain ⟨y,t,hy,ht,run⟩ := conjugationRun_writes body prime w prime_prime mat b proj unit r clock count copyPorts
    outside clockPivot H hm pool source apart q poolPivot srcPivot poolInv srcInv qPivot shared
    poolFree srcFree fits detFits u B ready
  let F := {B with R := Function.update B.R (q 3) (matrixWords prime H (mat b * mat proj * (mat b)⁻¹) ++ B.R (q 3))}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body packed y F
  have len : (F.R packed).length = m*m*H := by
    simp only [F,B,Function.update_of_ne distinct,Function.update_self,length_matrixWords]
  refine ⟨z,n+(t+(2*(F.R packed).length+2)),hz.trans (hy.trans hu),?_,Exec.seq read (Exec.seq run ?_)⟩
  · rw [len,Nat.add_assoc]
    exact Nat.add_le_add hn (Nat.add_le_add_right ht _)
  · simpa only [F,B,Function.update_of_ne distinct.symm,Function.update_comm distinct.symm,
      Function.update_idem,← blank,Function.update_eq_self] using clear

theorem physicalConjugation_writes (body : P → Pr P T Q prime U)
    (w j : ℕ)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod (prime^(w+1)))) (b proj : ι) (label : mat b = physicalLabel m (w+1) j)
    (live : LabelStock.live m (w+1) 1 j = true)
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
    (ancestor tail : List (Fin (prime+4)))
    (srcFree : ∀ a i j, j = 1 ∨ j = 13 → source a i ≠ q j) :
    let num := fun i j : Fin m => numerator (matrixInput b) (matrixInput proj) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    (∀ i j, (num i j).depth ≤ D) →
    let f := determinant (matrixInput b)
    f.depth ≤ D →
    let C := 48*H*H+152*H+66
    Writes body (fun S => (fun R => R (a 2) = ancestor ++ (LabelDirectory.digits m (w+1) j).map RadixDigits.digitSymbol ++ tail ∧
      (R prefixWidth).length = ancestor.length ∧ (R (a 1)).length = w+1 ∧
      (∀ i : Fin 7, i = 0 ∨ 3 ≤ i → R (a i) = []) ∧ (R (digits 4)).length = H ∧
      (∀ i : Fin 6, i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 → R (digits i) = []) ∧ R zeros = binSyms H 0) S ∧ S packed = [] ∧
      (let R := Function.update S packed (matrixWords prime H (mat b))
       (R clock).length = w ∧ R count = [] ∧ R (r 14) = [] ∧
      R (r 15) = binSyms H (1 : ZMod (prime^(w+1))).val ∧ R (r 4) = binSyms H (prime^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → R (r i) = []) ∧
      (∀ k ≤ D, R (frame pool k 2) = binSyms H (prime^(w+1))) ∧
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame pool k i) = []) ∧
      (∀ a, leafReady (fun c _ => source c) mat H a (source a 3) R) ∧
      R (q 2) = binSyms H (prime^(w+1)) ∧ R (q 13) = [] ∧
      ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (q k) = [])) (q 3)
      (.seq (directoryMatrix m a digits prefixWidth zeros packed) (.seq (.seq (.seq (compile (readLeaf (leafBank source)) (registerBank pool) f 0 (r 14)) (reusablePivotInverse prime r clock count))
        (.seq (packedConjugate pool source q b proj) (.seq (bclear (r 0)) (bclear (r 14))))) (bclear packed)))
      (matrixWords prime H (mat b * mat proj * (mat b)⁻¹))
      ((m*(m*(12*ancestor.length+8*((w+1)*(m*m))+(w+1)*(7*H+prime+31)+10*H+42)+1)+1) + (time H (readTime H) f + (6*w+6+(14*H+16+(prime-2)*C+C+w*(12*H+15+prime*C))) +
       ((m*(m*(cost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) + (2*(m*m*H)+2))
 := by
  intro num cost fits f detFits C
  have pos : 0 < H := by
    have hp := pow_pos prime_prime.pos (w+1)
    by_contra! h
    rw [show H = 0 by omega,pow_zero] at hm
    omega
  have read := directoryMatrix_writes body a digits digitPort sep prefixWidth zeros packed
    ports external prefixAcc aOut bOut zeroPort m (w+1) j H pos ancestor tail
  rw [← label] at read
  exact physicalConjugationFromReader_writes body w j mat b proj label live r clock count copyPorts outside
    clockPivot H hm pool source apart q poolPivot srcPivot poolInv srcInv qPivot shared poolFree packed distinct
    _ _ _ read srcFree fits detFits

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
