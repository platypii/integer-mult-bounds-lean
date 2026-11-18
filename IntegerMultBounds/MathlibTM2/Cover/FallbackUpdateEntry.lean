module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDifference
public import IntegerMultBounds.MathlibTM2.Cover.FallbackMatrixRead
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Prepend one updated elimination entry to the next packed matrix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def updateReadPorts : Fin 8 ↪ Fin 17 := ⟨![3,2,15,1,4,5,6,13],by decide⟩

def updateEntry {d : ℕ} (j row pivot : Fin d) (r : Fin 17 ↪ Fin T) : Pr P T Q A U :=
  .seq (readColumnPair j row pivot (updateReadPorts.trans r))
    (.seq (subtractProduct ((Fin.castLEEmb (by decide)).trans r))
      (.seq (bcopy (r 14) (r 16) (r 4) (r 5)) (clearWords [r 1,r 13,r 14])))

theorem updateEntry_exec {M d : ℕ} [NeZero M] (body : P → Pr P T Q A U) (r : Fin 17 ↪ Fin T)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (j row pivot : Fin d) (c : ZMod M) (H : ℕ)
    (hm : M < 2^H) (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (matrix : S.R (r 15) = matrixWords A H m ++ tail) (modulus : S.R (r 2) = binSyms H M)
    (coeff : S.R (r 0) = binSyms H c.val) (free : ∀ i : Fin 17, 0 < i → i ≠ 2 → i < 15 → S.R (r i) = []) :
    let reads := 8*((pivot.val*d+j.val)*H)+14*H+22 + (8*((row.val*d+j.val)*H)+14*H+22)
    ∃ z n, z.user = v.user ∧ n ≤ reads+48*H*H+180*H+96 ∧
      Exec body (updateEntry j row pivot r) (mk v S) n
        (mk z {S with R := Function.update S.R (r 16) (binSyms H (m row j-c*m pivot j).val ++ S.R (r 16))}) := by
  have ports : ∀ i : Fin 8, i ≠ 1 → i ≠ 2 →
      0 < updateReadPorts i ∧ updateReadPorts i ≠ 2 ∧ updateReadPorts i < 15 := by decide
  obtain ⟨u,hu,read⟩ := readColumnPair_exec body (updateReadPorts.trans r) m j row pivot H v S tail matrix
    (by change (S.R (r 2)).length = H; simp [modulus,length_binSyms])
    (fun i a b => free _ (ports i a b).1 (ports i a b).2.1 (ports i a b).2.2)
  let D : Stacks T A := {S with R := Function.update (Function.update S.R (r 1)
    (binSyms H (m pivot j).val)) (r 13) (binSyms H (m row j).val)}
  have keep (i : Fin 17) (h : i ≠ 1) (h' : i ≠ 13) : D.R (r i) = S.R (r i) := by
    simp [D,Function.update_of_ne (r.injective.ne h),Function.update_of_ne (r.injective.ne h')]
  let bank : Fin 15 ↪ Fin 17 := Fin.castLEEmb (by decide)
  obtain ⟨y,l,hy,hl,sub⟩ := subtractProduct_exec body (bank.trans r) H hm (m row j) c (m pivot j) u D
    ((keep 0 (by decide) (by decide)).trans coeff) (by change D.R (r 1) = _; simp [D,r.injective.eq_iff])
    ((keep 2 (by decide) (by decide)).trans modulus) (by change D.R (r 13) = _; simp [D])
    (by
      intro i lo h
      apply (keep (bank i) _ (fun e => h (bank.injective e))).trans (free _ _ _ i.isLt)
      all_goals change 3 ≤ i.val at lo; first | exact Nat.zero_lt_of_lt lo | intro e; have := congrArg Fin.val e; change i.val = _ at this; omega)
  let result := binSyms (A := A) H (m row j-c*m pivot j).val
  let E : Stacks T A := {D with R := Function.update D.R (r 14) result}
  obtain ⟨s,hs,copy⟩ := bcopy_exec body (a := r 14) (c := r 16) (t₁ := r 4) (t₂ := r 5)
    (by simp [List.nodup_cons,r.injective.eq_iff]) y E
    (by simp [E,D,r.injective.eq_iff,free 4 (by decide) (by decide) (by decide)])
    (by simp [E,D,r.injective.eq_iff,free 5 (by decide) (by decide) (by decide)])
  let F : Stacks T A := {E with R := Function.update E.R (r 16) (result ++ S.R (r 16))}
  obtain ⟨z,hz,clear⟩ := clearWords_exec (body := body) [r 1,r 13,r 14]
    (by simp [List.nodup_cons,r.injective.eq_iff]) s F
  simp [E,D,r.injective.eq_iff,result,length_binSyms] at copy
  simp [F,E,D,r.injective.eq_iff,result,length_binSyms] at clear
  refine ⟨z,_,hz.trans (hs.trans (hy.trans hu)),?_,(Exec.seq read (Exec.seq sub (Exec.seq copy clear))).cast rfl ?_⟩
  · omega
  · congr 1
    refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
    funext k
    by_cases a : k = r 1
    · subst k; simp [r.injective.eq_iff,free 1 (by decide) (by decide) (by decide)]
    by_cases b : k = r 13
    · subst k; simp [r.injective.eq_iff,free 13 (by decide) (by decide) (by decide)]
    by_cases e : k = r 14
    · subst k; simp [r.injective.eq_iff,free 14 (by decide) (by decide) (by decide)]
    by_cases o : k = r 16 <;> simp [o,a,b,e,r.injective.eq_iff]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
