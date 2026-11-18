module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackUpdateRow

/-! Compute the row multiplier once and emit the whole updated row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.ShortConv
variable {T Q A d M : ℕ} [NeZero M] {P U : Type}

def multiplierReadPorts : Fin 7 ↪ Fin 19 := ⟨![3,2,15,18,4,5,6],by decide⟩

def eliminateRow (k row pivot : Fin d) (r : Fin 19 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord (row.val*d+k.val) (multiplierReadPorts.trans r))
    (.seq (bmodmul (r 18) (r 17) (r 2) (r 0) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9) (r 10) (r 11) (r 12))
      (.seq (updateRow row pivot ((Fin.castLEEmb (by decide)).trans r)) (clearWords [r 0,r 18])))

theorem eliminateRow_exec (body : P → Pr P T Q A U) (r : Fin 19 ↪ Fin T)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (k row pivot : Fin d) (inv : ZMod M) (H : ℕ)
    (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H M)
    (inverse : S.R (r 17) = binSyms H inv.val)
    (free : ∀ i : Fin 19, (i < 15 ∧ i ≠ 2) ∨ i = 18 → S.R (r i) = []) :
    let words := List.ofFn fun j => binSyms (A := A) H (m row j-m row k*inv*m pivot j).val
    ∃ z n, z.user = v.user ∧ n ≤ 8*((row.val*d+k.val)*H)+48*H*H+168*H+92+d*entryTime d H ∧
      Exec body (eliminateRow k row pivot r) (mk v S) n
        (mk z {S with R := Function.update S.R (r 16) (words.flatten ++ S.R (r 16))}) := by
  have ports : ∀ i : Fin 7, i = 0 ∨ 4 ≤ i → multiplierReadPorts i < 15 ∧ multiplierReadPorts i ≠ 2 := by decide
  obtain ⟨u,hu,read⟩ := readMatrixWord_exec body (multiplierReadPorts.trans r) m row k H v S tail matrix
    (by change (S.R (r 2)).length = H; simp [modulus,length_binSyms])
    (fun i h => free _ (Or.inl (ports i h)))
  change Exec _ _ _ _ (mk u {S with R := Function.update S.R (r 18) (_ ++ S.R (r 18))}) at read
  rw [free 18 (by decide),List.append_nil] at read
  let D : Stacks T A := {S with R := Function.update S.R (r 18) (binSyms H (m row k).val)}
  have keep (i : Fin 19) (h : i ≠ 18) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne h) _ _
  have blank (i : Fin 19) (h : i < 15) (h' : i ≠ 2) := (keep i (by omega)).trans (free i (.inl ⟨h,h'⟩))
  obtain ⟨y,n,hy,hn,mul⟩ := bmodmul_exec body (a := r 18) (b := r 17) (m := r 2) (c := r 0)
    (p := r 4) (qq := r 5) (s := r 6) (rr := r 7) (t := r 8) (tx := r 9) (ty := r 10)
    (tz := r 11) (cy := r 12) (by simp [List.nodup_cons,r.injective.eq_iff])
    (r.injective.ne (by decide)) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    ((m row k).val_lt.trans hm) (inv.val_lt.trans hm) hm (NeZero.pos M) u D (by simp [D])
    ((keep 17 (by decide)).trans inverse) ((keep 2 (by decide)).trans modulus)
    (blank 4 (by decide) (by decide)) (blank 5 (by decide) (by decide)) (blank 6 (by decide) (by decide))
    (blank 7 (by decide) (by decide)) (blank 8 (by decide) (by decide)) (blank 9 (by decide) (by decide))
    (blank 10 (by decide) (by decide)) (blank 11 (by decide) (by decide))
  rw [blank 0 (by decide) (by decide),List.append_nil,← ZMod.val_mul] at mul
  let E : Stacks T A := {D with R := Function.update D.R (r 0) (binSyms H (m row k*inv).val)}
  have kept (i : Fin 19) (h : i ≠ 0) (h' : i ≠ 18) : E.R (r i) = S.R (r i) :=
    (Function.update_of_ne (r.injective.ne h) _ _).trans (keep i h')
  let bank : Fin 17 ↪ Fin 19 := Fin.castLEEmb (by decide)
  obtain ⟨z,l,hz,hl,emit⟩ := updateRow_exec body (bank.trans r) m row pivot (m row k*inv) H hm y E tail
    ((kept 15 (by decide) (by decide)).trans matrix) ((kept 2 (by decide) (by decide)).trans modulus)
    (by change E.R (r 0) = _; simp [E]) (by
      intro i lo h hi
      apply (kept (bank i) (fun e => lo.ne' (bank.injective e)) _).trans (free _ (.inl ⟨hi,fun e => h (bank.injective e)⟩))
      intro e; have q := congrArg Fin.val e; change i.val = 18 at q; omega)
  let words := List.ofFn fun j => binSyms (A := A) H (m row j-m row k*inv*m pivot j).val
  change Exec _ _ _ _ (mk z {E with R := Function.update E.R (r 16) (words.flatten ++ E.R (r 16))}) at emit
  rw [kept 16 (by decide) (by decide)] at emit
  let F : Stacks T A := {E with R := Function.update E.R (r 16) (words.flatten ++ E.R (r 16))}
  obtain ⟨z',hz',clear⟩ := clearWords_exec (body := body) [r 0,r 18]
    (by simp [List.nodup_cons,r.injective.eq_iff]) z F
  simp [F,E,D,r.injective.eq_iff,length_binSyms] at clear
  refine ⟨z',_,hz'.trans (hz.trans (hy.trans hu)),?_,(Exec.seq read (Exec.seq mul (Exec.seq emit clear))).cast rfl ?_⟩
  · nlinarith only [hl,hn]
  · congr 1
    refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
    funext i
    by_cases h : i = r 0
    · subst i; simp [r.injective.eq_iff,free 0 (by decide)]
    by_cases h' : i = r 18
    · subst i; simp [r.injective.eq_iff,free 18 (by decide)]
    by_cases e : i = r 16 <;> simp [h,h',e,r.injective.eq_iff,words]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
