module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDeterminantFormula
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDifference
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! The two arithmetic instructions of a determinant formula use the same register bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A M : ℕ} [NeZero M] {P U : Type}

inductive Gate where
  | sub
  | mul

def Gate.apply (op : Gate) (x y : ZMod M) := match op with
  | .sub => x-y
  | .mul => x*y

def Gate.program (op : Gate) (r : Fin 13 ↪ Fin T) : Pr P T Q A U := match op with
  | .sub => difference ((Fin.castLEEmb (by decide)).trans r)
  | .mul => bmodmul (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12)

def Gate.time (op : Gate) (H : ℕ) := match op with
  | .sub => 16*H+17
  | .mul => 48*H*H+150*H+64

theorem Gate.exec (op : Gate) (body : P → Pr P T Q A U) (r : Fin 13 ↪ Fin T)
    (H : ℕ) (hm : M < 2^H) (x y : ZMod M) (v : HS T Q A U) (S : Stacks T A)
    (left : S.R (r 0) = binSyms H x.val) (right : S.R (r 1) = binSyms H y.val)
    (modulus : S.R (r 2) = binSyms H M) (free : ∀ i : Fin 13, 3 ≤ i → i < 12 → S.R (r i) = []) :
    ∃ z n, z.user = v.user ∧ n ≤ op.time H ∧ Exec body (op.program r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 3) (binSyms H (op.apply x y).val)}) := by
  cases op with
  | sub =>
    exact difference_exec body _ H hm x y v S left right modulus
      (fun i lo hi => free (i.castLE (by decide)) lo (by change i.val < 12; omega))
  | mul =>
    obtain ⟨z,n,hz,hn,run⟩ := bmodmul_exec body (a := r 0) (b := r 1) (m := r 2) (c := r 3)
      (p := r 4) (qq := r 5) (s := r 6) (rr := r 7) (t := r 8) (tx := r 9) (ty := r 10)
      (tz := r 11) (cy := r 12) (by simp [List.nodup_cons,r.injective.eq_iff])
      (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide))
      (x.val_lt.trans hm) (y.val_lt.trans hm) hm (NeZero.pos M) v S left right modulus
      (free 4 (by decide) (by decide)) (free 5 (by decide) (by decide)) (free 6 (by decide) (by decide))
      (free 7 (by decide) (by decide)) (free 8 (by decide) (by decide)) (free 9 (by decide) (by decide))
      (free 10 (by decide) (by decide)) (free 11 (by decide) (by decide))
    rw [free 3 (by decide) (by decide),List.append_nil,← ZMod.val_mul] at run
    exact ⟨z,n,hz,by dsimp [time]; nlinarith only [hn],run⟩

open Mult.ShortConv LabelTraversal Node

def Gate.combine (op : Gate) (r : Fin 13 ↪ Fin T) (left right : Pr P T Q A U) : Pr P T Q A U :=
  .seq left (.seq right (.seq (op.program r) (clearWords [r 0,r 1])))

theorem Gate.combine_writes (op : Gate) (body : P → Pr P T Q A U) (r : Fin 13 ↪ Fin T)
    (H : ℕ) (hm : M < 2^H) (x y : ZMod M) (p q : Pr P T Q A U) (cp cq : ℕ)
    (pre next : Regs T A → Prop)
    (left : Writes body pre (r 0) p (binSyms H x.val) cp)
    (right : Writes body next (r 1) q (binSyms H y.val) cq)
    (afterLeft : ∀ R, pre R → next (Function.update R (r 0) (binSyms H x.val))) :
    Writes body (fun R => pre R ∧ R (r 2) = binSyms H M ∧
      ∀ i : Fin 13, i ≠ 2 → i < 12 → R (r i) = []) (r 3) (op.combine r p q)
      (binSyms H (op.apply x y).val) (cp+cq+op.time H+4*H+5) := by
  intro v S ⟨valid,modulus,free⟩
  obtain ⟨u,l,hu,hl,a⟩ := left v S valid
  rw [free 0 (by decide) (by decide),List.append_nil] at a
  let D := {S with R := Function.update S.R (r 0) (binSyms H x.val)}
  obtain ⟨y',k,hy,hk,b⟩ := right u D (afterLeft _ valid)
  have empty : D.R (r 1) = [] := by simp [D,r.injective.eq_iff,free 1 (by decide) (by decide)]
  rw [empty,List.append_nil] at b
  let E := {D with R := Function.update D.R (r 1) (binSyms H y.val)}
  have keep (i : Fin 13) (h : i ≠ 0) (h' : i ≠ 1) : E.R (r i) = S.R (r i) := by
    simp [E,D,Function.update_of_ne (r.injective.ne h),Function.update_of_ne (r.injective.ne h')]
  obtain ⟨t,n,ht,hn,compute⟩ := op.exec body r H hm x y y' E (by simp [E,D,r.injective.eq_iff])
    (Function.update_self ..) ((keep 2 (by decide) (by decide)).trans modulus)
    (fun i lo hi => (keep i (by omega) (by omega)).trans (free i (by omega) hi))
  let F := {E with R := Function.update E.R (r 3) (binSyms H (op.apply x y).val)}
  obtain ⟨z,hz,clear⟩ := clearWords_exec (body := body) [r 0,r 1] (by simp [r.injective.eq_iff]) t F
  simp [F,E,D,r.injective.eq_iff,length_binSyms] at clear
  refine ⟨z,_,hz.trans (ht.trans (hy.trans hu)),by omega,(Exec.seq a (Exec.seq b (Exec.seq compute clear))).cast rfl ?_⟩
  rw [free 3 (by decide) (by decide),List.append_nil]
  congr 1
  refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
  funext i
  by_cases a : i = r 0
  · subst i; simp [r.injective.eq_iff,free 0 (by decide) (by decide)]
  by_cases b : i = r 1
  · subst i; simp [r.injective.eq_iff,free 1 (by decide) (by decide)]
  by_cases c : i = r 3 <;> simp [a,b,c,r.injective.eq_iff]

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
