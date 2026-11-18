module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackProjectorEntries
public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv

/-! Emit an off-diagonal block entry from a packed projector and a tape weight. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
variable {T Q A d M : ℕ} [NeZero M] {P U : Type}

def weightedReadPorts : Fin 7 ↪ Fin 14 := ⟨![4,2,13,1,5,6,7],by decide⟩

def weightedEntry (offset : ℕ) (r : Fin 14 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord offset (weightedReadPorts.trans r)) (.seq
    (bmodmul (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12))
    (bclear (r 1)))

theorem weightedEntry_writes (body : P → Pr P T Q A U) (r : Fin 14 ↪ Fin T)
    (B : Matrix (Fin d) (Fin d) (ZMod M)) (i j : Fin d) (weight : ZMod M) (H : ℕ) (hm : M < 2^H)
    (tail : List (Fin (A+4))) :
    Writes body (fun R => R (r 13) = matrixWords A H B ++ tail ∧ R (r 0) = binSyms H weight.val ∧
      R (r 2) = binSyms H M ∧ ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (r k) = [])
      (r 3) (weightedEntry (i.val*d+j.val) r) (binSyms H (weight * B i j).val)
      (8*((i.val*d+j.val)*H)+48*H*H+166*H+88) := by
  intro v S ⟨matrix,coeff,modulus,free⟩
  have scratch : ∀ k : Fin 7, k = 0 ∨ 4 ≤ k → 4 ≤ weightedReadPorts k ∧ weightedReadPorts k < 12 := by decide
  obtain ⟨u,hu,read⟩ := readMatrixWord_exec body (weightedReadPorts.trans r) B i j H v S tail matrix
    ((congrArg List.length modulus).trans (length_binSyms ..)) (fun k h => free _ (.inr (scratch k h)))
  change Exec _ _ _ _ (mk u {S with R := Function.update S.R (r 1) (_ ++ S.R (r 1))}) at read
  rw [free 1 (by decide),List.append_nil] at read
  let D : Stacks T A := {S with R := Function.update S.R (r 1) (binSyms H (B i j).val)}
  have keep (k : Fin 14) (h : k ≠ 1) : D.R (r k) = S.R (r k) := Function.update_of_ne (r.injective.ne h) _ _
  have work (k : Fin 14) (h : 4 ≤ k ∧ k < 12) := (keep k (by omega)).trans (free k (.inr h))
  obtain ⟨y,n,hy,hn,mul⟩ := bmodmul_exec body (a := r 0) (b := r 1) (m := r 2) (c := r 3)
    (p := r 4) (qq := r 5) (s := r 6) (rr := r 7) (t := r 8) (tx := r 9) (ty := r 10)
    (tz := r 11) (cy := r 12) (by simp [List.nodup_cons,r.injective.eq_iff])
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    (weight.val_lt.trans hm) ((B i j).val_lt.trans hm) hm (NeZero.pos M) u D ((keep 0 (by decide)).trans coeff)
    (Function.update_self ..) ((keep 2 (by decide)).trans modulus) (work 4 (by decide)) (work 5 (by decide))
    (work 6 (by decide)) (work 7 (by decide)) (work 8 (by decide)) (work 9 (by decide)) (work 10 (by decide)) (work 11 (by decide))
  rw [← ZMod.val_mul,keep 3 (by decide)] at mul
  let output := binSyms (A := A) H (weight * B i j).val ++ S.R (r 3)
  let E : Stacks T A := {D with R := Function.update D.R (r 3) output}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 1) y E
  have finish : Function.update E.R (r 1) [] = Function.update S.R (r 3) output := by
    funext k
    by_cases a : k = r 1 <;> by_cases b : k = r 3 <;> simp_all [E,D,r.injective.eq_iff,free 1 (by decide)]
  refine ⟨z,_,hz.trans (hy.trans hu),?_,(Exec.seq read (Exec.seq mul clear)).cast rfl ?_⟩
  · simp [E,D,r.injective.eq_iff,length_binSyms]
    nlinarith only [hn]
  · rw [← finish]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
