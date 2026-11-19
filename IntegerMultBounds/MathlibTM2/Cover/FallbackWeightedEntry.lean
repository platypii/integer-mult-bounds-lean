module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackProjectorEntries
public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv

/-! Emit an off-diagonal block entry from a packed projector and a tape weight. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
variable {T Q A d M : ℕ} [NeZero M] {P U : Type}

def weightedReadPorts : Fin 7 ↪ Fin 14 := ⟨![4,2,13,1,5,6,7],by decide⟩

def scaleEntry (entry : Pr P T Q A U) (r : Fin 13 ↪ Fin T) : Pr P T Q A U :=
  .seq entry (.seq
    (bmodmul (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12))
    (bclear (r 1)))

theorem scaleEntry_writes (body : P → Pr P T Q A U) (r : Fin 13 ↪ Fin T)
    (entry : Pr P T Q A U) (ok : Node.Regs T A → Prop) (x weight : ZMod M) (H c : ℕ) (hm : M < 2^H)
    (emit : Writes body ok (r 1) entry (binSyms H x.val) c) :
    Writes body (fun R => ok R ∧ R (r 0) = binSyms H weight.val ∧ R (r 2) = binSyms H M ∧
      ∀ k : Fin 13, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (r k) = [])
      (r 3) (scaleEntry entry r) (binSyms H (weight*x).val) (c+48*H*H+152*H+66) := by
  intro v S ⟨valid,coeff,modulus,free⟩
  obtain ⟨u,t,hu,ht,read⟩ := emit v S valid
  change Exec _ _ _ _ (mk u {S with R := Function.update S.R (r 1) (_ ++ S.R (r 1))}) at read
  rw [free 1 (by decide),List.append_nil] at read
  let D : Stacks T A := {S with R := Function.update S.R (r 1) (binSyms H x.val)}
  have keep (k : Fin 13) (h : k ≠ 1) : D.R (r k) = S.R (r k) := Function.update_of_ne (r.injective.ne h) _ _
  have work (k : Fin 13) (h : 4 ≤ k ∧ k < 12) := (keep k (by omega)).trans (free k (.inr h))
  obtain ⟨y,n,hy,hn,mul⟩ := bmodmul_exec body (a := r 0) (b := r 1) (m := r 2) (c := r 3)
    (p := r 4) (qq := r 5) (s := r 6) (rr := r 7) (t := r 8) (tx := r 9) (ty := r 10)
    (tz := r 11) (cy := r 12) (by simp [List.nodup_cons,r.injective.eq_iff])
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    (weight.val_lt.trans hm) (x.val_lt.trans hm) hm (NeZero.pos M) u D ((keep 0 (by decide)).trans coeff)
    (Function.update_self ..) ((keep 2 (by decide)).trans modulus) (work 4 (by decide)) (work 5 (by decide))
    (work 6 (by decide)) (work 7 (by decide)) (work 8 (by decide)) (work 9 (by decide)) (work 10 (by decide)) (work 11 (by decide))
  rw [← ZMod.val_mul,keep 3 (by decide)] at mul
  let output := binSyms (A := A) H (weight*x).val ++ S.R (r 3)
  let E : Stacks T A := {D with R := Function.update D.R (r 3) output}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 1) y E
  have finish : Function.update E.R (r 1) [] = Function.update S.R (r 3) output := by
    funext k
    by_cases a : k = r 1 <;> by_cases b : k = r 3 <;> simp_all [E,D,r.injective.eq_iff,free 1 (by decide)]
  refine ⟨z,_,hz.trans (hy.trans hu),?_,(Exec.seq read (Exec.seq mul clear)).cast rfl ?_⟩
  · simp [E,D,r.injective.eq_iff,length_binSyms]
    nlinarith only [hn,ht]
  · rw [← finish]

def weightedEntry (offset : ℕ) (r : Fin 14 ↪ Fin T) : Pr P T Q A U :=
  scaleEntry (readMatrixWord offset (weightedReadPorts.trans r)) ((Fin.castLEEmb (by decide)).trans r)

theorem weightedEntry_writes {e : ℕ} (body : P → Pr P T Q A U) (r : Fin 14 ↪ Fin T)
    (B : Matrix (Fin d) (Fin e) (ZMod M)) (i : Fin d) (j : Fin e) (weight : ZMod M) (H : ℕ) (hm : M < 2^H)
    (tail : List (Fin (A+4))) :
    Writes body (fun R => R (r 13) = matrixWords A H B ++ tail ∧ R (r 0) = binSyms H weight.val ∧
      R (r 2) = binSyms H M ∧ ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (r k) = [])
      (r 3) (weightedEntry (i.val*e+j.val) r) (binSyms H (weight * B i j).val)
      (8*((i.val*e+j.val)*H)+48*H*H+166*H+88) := by
  intro v S ⟨matrix,coeff,modulus,free⟩
  have scratch : ∀ k : Fin 7, k = 0 ∨ 4 ≤ k → 4 ≤ weightedReadPorts k ∧ weightedReadPorts k < 12 := by decide
  let bank : Fin 13 ↪ Fin T := (Fin.castLEEmb (by decide)).trans r
  let cost := 8*((i.val*e+j.val)*H)+14*H+22
  have emit : Writes body (fun R => R = S.R) (bank 1) (readMatrixWord (i.val*e+j.val) (weightedReadPorts.trans r))
      (binSyms H (B i j).val) cost := by
    intro z F eq
    obtain ⟨y,hy,run⟩ := readMatrixWord_exec body (weightedReadPorts.trans r) B i j H z F tail (eq ▸ matrix)
      ((congrArg List.length (eq ▸ modulus)).trans (length_binSyms ..))
      (fun k h => eq ▸ free _ (.inr (scratch k h)))
    exact ⟨y,_,hy,le_rfl,run⟩
  obtain ⟨z,n,hz,hn,run⟩ := scaleEntry_writes body bank _ _ (B i j) weight H cost hm emit v S
    ⟨rfl,coeff,modulus,fun k h => free (k.castLE (by decide)) (by
      rcases h with h | h
      · subst k; decide
      · exact .inr ⟨h.1,h.2⟩)⟩
  exact ⟨z,n,hz,by dsimp [cost] at hn; omega,run⟩

/-- Multiply the incoming weight by the selected pivot in the packed child record. -/
theorem childWeight_writes (body : P → Pr P T Q A U) (r : Fin 14 ↪ Fin T)
    (pivot : Fin d → ZMod M) (i : Fin d) (weight : ZMod M) (H : ℕ) (hm : M < 2^H)
    (tail : List (Fin (A+4))) :
    Writes body (fun R => R (r 13) = (List.ofFn fun j => binSyms H (pivot j).val).flatten ++ tail ∧
      R (r 0) = binSyms H weight.val ∧ R (r 2) = binSyms H M ∧
      ∀ k : Fin 14, k = 1 ∨ 4 ≤ k ∧ k < 12 → R (r k) = [])
      (r 3) (weightedEntry i.val r) (binSyms H (weight * pivot i).val)
      (8*(i.val*H)+48*H*H+166*H+88) := by
  let row : Matrix (Fin 1) (Fin d) (ZMod M) := fun _ j => pivot j
  simpa [matrixWords, List.ofFn_succ, row] using
    weightedEntry_writes body r row 0 i weight H hm tail

end IntegerMultBounds.MathlibTM2.Cover.Fallback
