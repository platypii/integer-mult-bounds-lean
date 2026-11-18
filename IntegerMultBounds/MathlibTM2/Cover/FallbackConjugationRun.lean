module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPackedConjugate
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDenominator

/-! Compute packed matrix conjugation, including the reciprocal and register cleanup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι P U : Type} {T Q A m D : ℕ}

theorem conjugationRun_writes (body : P → Pr P T Q A U)
    (ports : Leaf (Entry ι m) → Fin T → Fin 7 ↪ Fin T) (bank : ℕ → Fin T → Fin 13 ↪ Fin T)
    (p w : ℕ) (hp : p.Prime) [NeZero (p^(w+1))]
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod (p^(w+1)))) (b proj : ι) (unit : IsUnit (mat b).det)
    (r : Fin 16 ↪ Fin T) (clock count : Fin T) (copyPorts : [clock,count,r 2,r 3].Nodup)
    (outside : ∀ i, r i ≠ count) (clockPivot : clock ≠ r 14)
    (H : ℕ) (hm : p^(w+1) < 2^H)
    (pool : Fin ((D+1)*13) ↪ Fin T) (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T)
    (apart : ∀ a i j, source a i ≠ pool j) (q : Fin 14 ↪ Fin T)
    (shared : q 0 = r 0) (dst : q 3 ≠ r 14)
    (poolFree : ∀ k j, j = 1 ∨ j = 13 → pool k ≠ q j)
    (srcFree : ∀ a i j, j = 1 ∨ j = 13 → source a i ≠ q j) :
    let num := fun i j : Fin m => numerator (matrixInput b) (matrixInput proj) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (num ij.1 ij.2)
    (∀ i j, (num i j).depth ≤ D) →
    let f := determinant (matrixInput b)
    let C := 48*H*H+152*H+66
    Writes body (fun R => (R clock).length = w ∧ R count = [] ∧ R (r 14) = [] ∧
      R (r 15) = binSyms H (1 : ZMod (p^(w+1))).val ∧ R (r 4) = binSyms H (p^(w+1)) ∧
      (∀ i : Fin 16, i ≠ 4 → i < 13 → R (r i) = []) ∧
      prepared bank (entryValue mat) H (leafReady ports mat H) f 0 (r 14) R ∧
      (let B := Function.update (Function.update R (r 14) (binSyms H (mat b).det.val)) (r 0)
          (binSyms H (Ring.inverse (mat b).det).val)
       (∀ k ≤ D, B (frame pool k 2) = binSyms H (p^(w+1))) ∧
       (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → B (frame pool k i) = []) ∧
       (∀ a, leafReady (fun c _ => source c) mat H a (source a 3) B) ∧
       B (q 2) = binSyms H (p^(w+1)) ∧ B (q 13) = [] ∧
       ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → B (q k) = [])) (q 3)
      (.seq (.seq (compile (readLeaf ports) bank f 0 (r 14)) (reusablePivotInverse p r clock count))
        (.seq (packedConjugate pool source q b proj) (.seq (bclear (r 0)) (bclear (r 14)))))
      (matrixWords A H (mat b * mat proj * (mat b)⁻¹))
      (time H (readTime H) f + (6*w+6+(14*H+16+(p-2)*C+C+w*(12*H+15+p*C))) +
       ((m*(m*(cost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) + 4*H+4) := by
  intro num cost fits f C v S ⟨ticks,countBlank,pivot,oneWord,modulus,free,ready,
    moduli,frames,inputs,modQ,blankQ,freeQ⟩
  have run := packedConjugate_writes body pool source apart mat b proj H hm q poolFree srcFree fits
  exact withDenominator_writes body ports bank p w hp mat b unit r clock count copyPorts outside clockPivot H hm
    (q 3) (shared ▸ q.injective.ne (by decide : (3 : Fin 14) ≠ 0)) dst _ _ _ _ run v S
    ⟨ticks,countBlank,pivot,oneWord,modulus,free,ready,moduli,frames,inputs,
      by rw [shared,Function.update_self],modQ,blankQ,freeQ⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
