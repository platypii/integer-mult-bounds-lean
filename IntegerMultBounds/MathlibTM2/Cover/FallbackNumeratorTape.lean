module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaLayout
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove

/-! Evaluate all Cramer numerators on one workspace and prepend them in matrix order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {ι : Type} {T Q A M m D : ℕ} [NeZero M] {P U : Type}

theorem numeratorTape_writes (body : P → Pr P T Q A U) (pool : Fin ((D+1)*13) ↪ Fin T)
    (source : Leaf (Entry ι m) → Fin 7 ↪ Fin T) (apart : ∀ a i j, source a i ≠ pool j)
    (mat : ι → Matrix (Fin m) (Fin m) (ZMod M)) (g proj : ι) (H : ℕ) (hm : M < 2^H)
    (value tmp out : Fin T) (regs : [value,tmp,out].Nodup)
    (valuePool : ∀ k, pool k ≠ value) (valueSrc : ∀ a i, source a i ≠ value)
    (outPool : ∀ k, pool k ≠ out) (outSrc : ∀ a i, source a i ≠ out) :
    let f := fun i j : Fin m => numerator (matrixInput g) (matrixInput proj) i j
    let cost := Finset.univ.sup fun ij : Fin m × Fin m => time H (readTime H) (f ij.1 ij.2)
    (∀ i j, (f i j).depth ≤ D) →
    Writes body (fun R => R value = [] ∧ R tmp = [] ∧
      (∀ k ≤ D, R (frame pool k 2) = binSyms H M) ∧
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → R (frame pool k i) = []) ∧
      ∀ a, leafReady (fun b _ => source b) mat H a (source a 3) R) out
      (sequence (fun i => sequence (fun j => .seq
        (compile (readLeaf (leafBank source)) (registerBank pool) (f i j) 0 value)
        (moveRightOrdered value tmp out)) (List.finRange m)) (List.finRange m))
      (matrixWords A H (conjugateNumerator (mat g) (mat proj))) (m*(m*(cost+4*H+4)+1)+1) := by
  intro f cost fits
  regs_ne regs
  apply matrixWords_writes
  · intro R xs h
    obtain ⟨empty,blank,modulus,free,inputs⟩ := h
    have kp (k i) : Function.update R out xs (frame pool k i) = R (frame pool k i) := Function.update_of_ne (outPool _) _ _
    have ks (a i) := Function.update_of_ne (outSrc a i) xs R
    refine ⟨(Function.update_of_ne ‹value ≠ out› _ _).trans empty,(Function.update_of_ne ‹tmp ≠ out› _ _).trans blank,
      fun k hk => (kp k 2).trans (modulus k hk),fun k hk i hi => (kp k i).trans (free k hk i hi),?_⟩
    intro a
    have src := inputs a
    refine ⟨rfl,?_⟩
    cases a with
    | input a =>
      obtain ⟨b,i,j⟩ := a
      obtain ⟨_,⟨tail,h⟩,width,work⟩ := src
      exact ⟨⟨tail,(ks _ 2).trans h⟩,(congrArg List.length (ks _ 1)).trans width,fun k hk => (ks _ k).trans (work k hk)⟩
    | zero | one =>
      obtain ⟨_,h,w,s⟩ := src
      exact ⟨(ks _ 2).trans h,(ks _ 4).trans w,(ks _ 5).trans s⟩
  · intro i j v S ⟨empty,blank,modulus,free,inputs⟩
    obtain ⟨u,n,hu,hn,compute⟩ := allocated_writes body pool source apart mat H hm (f i j) (fits i j)
      value valuePool valueSrc v S ⟨empty,modulus,free,inputs⟩
    have same (k : ι) : (Matrix.of fun r c => mat k r c) = mat k := rfl
    simp only [f,eval_numerator,matrixInput,eval,entryValue,same,empty,List.append_nil] at compute
    let word := binSyms (A := A) H ((conjugateNumerator (mat g) (mat proj)) i j).val
    let B := {S with R := Function.update S.R value word}
    obtain ⟨z,hz,move⟩ := moveRightOrdered_exec (body := body) value tmp out ‹value ≠ tmp› ‹value ≠ out› ‹tmp ≠ out› u B
      ((Function.update_of_ne ‹value ≠ tmp›.symm _ _).trans blank)
    have cap : time H (readTime H) (f i j) ≤ cost := Finset.le_sup (f := fun ij : Fin m × Fin m => time H (readTime H) (f ij.1 ij.2)) (Finset.mem_univ (i,j))
    simp only [B,Function.update_self,Function.update_idem,Function.update_of_ne ‹value ≠ out›.symm,
      ← empty,Function.update_eq_self] at move
    refine ⟨z,_,hz.trans hu,?_,Exec.seq compute move⟩
    simp only [word,length_binSyms]
    omega

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
