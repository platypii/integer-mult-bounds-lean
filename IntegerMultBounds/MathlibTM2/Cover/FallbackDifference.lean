module

public import IntegerMultBounds.MathlibTM2.Host.BinArithDiv
public import Mathlib.Data.ZMod.Basic

/-! Modular subtraction for an elimination entry, using the borrow bit at the input width. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {P U : Type}

def difference (r : Fin 8 ↪ Fin T) : Pr P T Q A U :=
  .seq (bsub (r 0) (r 1) (r 3) (r 4) (r 5) (r 6) (r 7))
    (.cond (fun v => symBit (v.scan (r 7)))
      (baddTo (r 3) (r 2) (r 4) (r 5) (r 6) (r 7)) (.act .done))

theorem difference_exec {M : ℕ} [NeZero M] (body : P → Pr P T Q A U) (r : Fin 8 ↪ Fin T)
    (H : ℕ) (hm : M < 2^H) (x y : ZMod M) (v : HS T Q A U) (S : Stacks T A)
    (hx : S.R (r 0) = binSyms H x.val) (hy : S.R (r 1) = binSyms H y.val)
    (modulus : S.R (r 2) = binSyms H M)
    (free : ∀ i : Fin 8, 3 ≤ i → i ≤ 6 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 16*H+17 ∧ Exec body (difference r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 3) (binSyms H (x-y).val)}) := by
  have bx := x.val_lt.trans hm
  have by' := y.val_lt.trans hm
  obtain ⟨u,hu,borrow,_,sub⟩ := bsub_exec body (a := r 0) (b := r 1) (c := r 3)
    (tx := r 4) (ty := r 5) (tz := r 6) (cy := r 7) (by simp [List.nodup_cons,r.injective.eq_iff])
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) bx by' v S hx hy
    (free 4 (by decide) (by decide)) (free 5 (by decide) (by decide)) (free 6 (by decide) (by decide))
  rw [free 3 (by decide) (by decide),List.append_nil] at sub
  let a := (x.val+2^H-y.val)%2^H
  let D : Stacks T A := {S with R := Function.update S.R (r 3) (binSyms H a)}
  by_cases h : x.val < y.val
  · have ha : a = x.val+2^H-y.val := Nat.mod_eq_of_lt (by omega)
    have hval : (x-y).val = x.val+M-y.val := by
      have lt := y.val_lt
      rw [sub_eq_add_neg,ZMod.val_add,ZMod.neg_val',Nat.mod_eq_of_lt (show M-y.val < M by omega),Nat.mod_eq_of_lt (by omega)]
      omega
    obtain ⟨z,hz,_,_,add⟩ := baddTo_exec body (x := a) (a := r 3) (b := r 2) (tx := r 4) (ty := r 5)
      (tz := r 6) (cy := r 7) (by simp [List.nodup_cons,r.injective.eq_iff])
      (r.injective.ne (by decide)) (r.injective.ne (by decide)) (Nat.mod_lt _ (by positivity : 0 < 2^H))
      hm u D (by simp [D,a]) (by simpa [D,r.injective.eq_iff] using modulus)
      (by simpa [D,r.injective.eq_iff] using free 4 (by decide) (by decide))
      (by simpa [D,r.injective.eq_iff] using free 5 (by decide) (by decide))
      (by simpa [D,r.injective.eq_iff] using free 6 (by decide) (by decide))
    change Exec _ _ _ _ (mk z {D with R := Function.update D.R (r 3) (binSyms H ((a+M)%2^H))}) at add
    have val : (a+M)%2^H = (x-y).val := by
      rw [show a+M = (x.val+M-y.val)+2^H by have := y.val_lt; omega,Nat.add_mod_right,hval,Nat.mod_eq_of_lt (by omega)]
    rw [val] at add
    have run := Exec.cond_true (q := .act .done) (f := fun v => symBit (v.scan (r 7)))
      (by simp [borrow,h]) add
    refine ⟨z,(8*H+8)+(8*H+8+1),hz.trans hu,by omega,?_⟩
    simpa [difference,D,Function.update_idem] using Exec.seq sub run
  · have val : a = (x-y).val := by
      rw [ZMod.val_sub (by omega)]
      dsimp [a]
      rw [show x.val+2^H-y.val = (x.val-y.val)+2^H by omega,Nat.add_mod_right,Nat.mod_eq_of_lt (by omega)]
    have run := Exec.cond_false (p := baddTo (r 3) (r 2) (r 4) (r 5) (r 6) (r 7))
      (f := fun v => symBit (v.scan (r 7))) (by simp [borrow,h]) (Exec.act (body := body) .done (mk u D))
    refine ⟨u,(8*H+8)+(1+1),hu,by omega,?_⟩
    exact (Exec.seq sub run).cast rfl (by simp [Action.run,D,val])

def differencePorts : Fin 8 ↪ Fin 15 := ⟨![13,3,2,14,4,5,6,12],by decide⟩

def subtractProduct (r : Fin 15 ↪ Fin T) : Pr P T Q A U :=
  .seq (bmodmul (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12))
    (.seq (difference (differencePorts.trans r)) (bclear (r 3)))

theorem subtractProduct_exec {M : ℕ} [NeZero M] (body : P → Pr P T Q A U) (r : Fin 15 ↪ Fin T)
    (H : ℕ) (hm : M < 2^H) (x c y : ZMod M) (v : HS T Q A U) (S : Stacks T A)
    (coeff : S.R (r 0) = binSyms H c.val) (pivotEntry : S.R (r 1) = binSyms H y.val)
    (modulus : S.R (r 2) = binSyms H M) (entry : S.R (r 13) = binSyms H x.val)
    (free : ∀ i : Fin 15, 3 ≤ i → i ≠ 13 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ 48*H*H+168*H+83 ∧ Exec body (subtractProduct r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 14) (binSyms H (x-c*y).val)}) := by
  obtain ⟨u,n,hu,hn,mul⟩ := bmodmul_exec body (a := r 0) (b := r 1) (m := r 2) (c := r 3)
    (p := r 4) (qq := r 5) (s := r 6) (rr := r 7) (t := r 8) (tx := r 9) (ty := r 10)
    (tz := r 11) (cy := r 12) (by simp [List.nodup_cons,r.injective.eq_iff])
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    (c.val_lt.trans hm) (y.val_lt.trans hm) hm (NeZero.pos M) v S coeff pivotEntry modulus
    (free 4 (by decide) (by decide)) (free 5 (by decide) (by decide)) (free 6 (by decide) (by decide))
    (free 7 (by decide) (by decide)) (free 8 (by decide) (by decide)) (free 9 (by decide) (by decide))
    (free 10 (by decide) (by decide)) (free 11 (by decide) (by decide))
  rw [free 3 (by decide) (by decide),List.append_nil,← ZMod.val_mul] at mul
  let D : Stacks T A := {S with R := Function.update S.R (r 3) (binSyms H (c*y).val)}
  have keep (i : Fin 15) (h : i ≠ 3) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
  have ports : ∀ i : Fin 8, 3 ≤ i → i ≤ 6 →
      differencePorts i ≠ 3 ∧ 3 ≤ differencePorts i ∧ differencePorts i ≠ 13 := by decide
  obtain ⟨z,l,hz,hl,sub⟩ := difference_exec body (differencePorts.trans r) H hm x (c*y) u D
    ((keep 13 (by decide)).trans entry) (by change D.R (r 3) = _; simp [D])
    ((keep 2 (by decide)).trans modulus) (fun i h j => (keep _ (ports i h j).1).trans
      (free _ (ports i h j).2.1 (ports i h j).2.2))
  let E : Stacks T A := {D with R := Function.update D.R (r 14) (binSyms H (x-c*y).val)}
  obtain ⟨z',hz',_,clear⟩ := bclear_exec body (r 3) z E
  have len : (E.R (r 3)).length = H := by simp [E,D,r.injective.eq_iff,length_binSyms]
  rw [len] at clear
  refine ⟨z',n+(l+(2*H+2)),hz'.trans (hz.trans hu),by nlinarith only [hn,hl],
    (Exec.seq mul (Exec.seq sub clear)).cast rfl ?_⟩
  congr 1
  refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
  funext i
  by_cases h : i = r 3
  · subst i; simp [E,D,r.injective.eq_iff,free 3 (by decide) (by decide)]
  · by_cases j : i = r 14
    · subst i; simp [E,D,r.injective.eq_iff]
    · simp [E,D,h,j]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
