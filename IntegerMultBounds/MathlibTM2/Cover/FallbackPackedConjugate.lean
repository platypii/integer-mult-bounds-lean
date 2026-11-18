module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackNormalize
public import IntegerMultBounds.MathlibTM2.Cover.FallbackNumeratorTape

/-! Write a conjugated matrix from packed inputs using one reciprocal and one formula pool. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι P U : Type} {T Q A M m D : ℕ} [NeZero M]

noncomputable def packedConjugate (pool : Fin ((D+1)*13) ↪ Fin T) (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T)
    (r : Fin 14 ↪ Fin T) (g proj : ι) : Pr P T Q A U :=
  .seq (sequence (fun i => sequence (fun j => .seq
    (compile (readLeaf (leafBank source)) (registerBank pool)
      (numerator (matrixInput g) (matrixInput proj) i j) 0 (r 1))
    (moveRightOrdered (r 1) (r 4) (r 13))) (List.finRange m)) (List.finRange m))
    (.seq (sequence (fun i : Fin m => sequence (fun j : Fin m => weightedEntry (i.val*m+j.val) r)
      (List.finRange m)) (List.finRange m)) (bclear (r 13)))

theorem packedConjugate_writes (body : P → Pr P T Q A U) (pool : Fin ((D+1)*13) ↪ Fin T)
    (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T) (apart : ∀ a i j, source a i ≠ pool j)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (g proj : ι) (H : ℕ) (hm : M < 2^H)
    (r : Fin 14 ↪ Fin T) (poolFree : ∀ k j, j = 1 ∨ j = 13 → pool k ≠ r j)
    (srcFree : ∀ a i j, j = 1 ∨ j = 13 → source a i ≠ r j) :
    let f := fun i j : Fin m => numerator (matrixInput g) (matrixInput proj) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (f ij.1 ij.2)
    (∀ i j, (f i j).depth ≤ D) →
    Writes body (fun R => (∀ k ≤ D, R (frame pool k 2) = binSyms H M) ∧
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame pool k i) = []) ∧
      (∀ a, leafReady (fun b _ => source b) mat H a (source a 3) R) ∧
      R (r 0) = binSyms H (Ring.inverse (mat g).det).val ∧ R (r 2) = binSyms H M ∧
      R (r 13) = [] ∧ ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (r k) = []) (r 3)
      (packedConjugate pool source r g proj) (matrixWords A H (mat g * mat proj * (mat g)⁻¹))
      ((m*(m*(cost+4*H+4)+1)+1) + (m*(m*(8*(m*m*H)+48*H*H+166*H+88)+1)+1) + (2*(m*m*H)+2)) := by
  intro f cost fits v S ⟨moduli,frames,inputs,inv,modulus,blank,free⟩
  have generate := numeratorTape_writes body pool source apart mat g proj H hm (r 1) (r 4) (r 13)
    (by simp [r.injective.eq_iff]) (fun k => poolFree k 1 (Or.inl rfl))
    (fun a i => srcFree a i 1 (Or.inl rfl)) (fun k => poolFree k 13 (Or.inr rfl))
    (fun a i => srcFree a i 13 (Or.inr rfl)) fits
  exact normalizedNumerators_writes body r (mat g) (mat proj) H hm _ _ _ generate v S
    ⟨⟨free 1 (by decide),free 4 (by decide),moduli,frames,inputs⟩,blank,inv,modulus,free⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
