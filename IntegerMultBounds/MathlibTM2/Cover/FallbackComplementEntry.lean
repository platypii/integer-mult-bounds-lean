module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackWeightedEntry
public import IntegerMultBounds.MathlibTM2.Cover.FallbackDifference
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Emit an entry of the complementary projector, preserving the packed source. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Mult.ShortConv
variable {T Q A d M : ℕ} [NeZero M] {P U : Type}

def complementEntry (offset : ℕ) (r : Fin 14 ↪ Fin T) : Pr P T Q A U :=
  .seq (readMatrixWord offset (weightedReadPorts.trans r))
    (.seq (difference ((Fin.castLEEmb (by decide)).trans r))
      (.seq (bcopy (r 3) (r 8) (r 4) (r 5)) (clearWords [r 1,r 3])))

theorem complementEntry_writes (body : P → Pr P T Q A U) (r : Fin 14 ↪ Fin T)
    (B : Matrix (Fin d) (Fin d) (ZMod M)) (i j : Fin d) (H : ℕ) (hm : M < 2^H)
    (tail : List (Fin (A+4))) :
    Writes body (fun R => R (r 13) = matrixWords A H B ++ tail ∧
      R (r 0) = binSyms H ((1 : Matrix (Fin d) (Fin d) (ZMod M)) i j).val ∧ R (r 2) = binSyms H M ∧
      ∀ k : Fin 14, k = 1 ∨ 3 ≤ k ∧ k ≤ 7 → R (r k) = [])
      (r 8) (complementEntry (i.val*d+j.val) r) (binSyms H ((1-B) i j).val)
      (8*((i.val*d+j.val)*H)+40*H+50) := by
  intro v S ⟨matrix,delta,modulus,free⟩
  have scratch : ∀ k : Fin 7, k = 0 ∨ 4 ≤ k → 3 ≤ weightedReadPorts k ∧ weightedReadPorts k ≤ 7 := by decide
  obtain ⟨u,hu,read⟩ := readMatrixWord_exec body (weightedReadPorts.trans r) B i j H v S tail matrix
    ((congrArg List.length modulus).trans (length_binSyms ..)) (fun k h => free _ (.inr (scratch k h)))
  change Exec _ _ _ _ (mk u {S with R := Function.update S.R (r 1) (_ ++ S.R (r 1))}) at read
  rw [free 1 (by decide),List.append_nil] at read
  let D : Stacks T A := {S with R := Function.update S.R (r 1) (binSyms H (B i j).val)}
  have keep (k : Fin 14) (h : k ≠ 1) : D.R (r k) = S.R (r k) := Function.update_of_ne (r.injective.ne h) _ _
  let bank : Fin 8 ↪ Fin 14 := Fin.castLEEmb (by decide)
  have work : ∀ k : Fin 8, 3 ≤ k → k ≤ 6 → bank k ≠ 1 ∧ 3 ≤ bank k ∧ bank k ≤ 7 := by decide
  obtain ⟨y,l,hy,hl,sub⟩ := difference_exec body (bank.trans r) H hm ((1 : Matrix _ _ (ZMod M)) i j)
    (B i j) u D ((keep 0 (by decide)).trans delta) (Function.update_self ..) ((keep 2 (by decide)).trans modulus)
    (fun k lo hi => (keep _ (work k lo hi).1).trans (free _ (.inr (work k lo hi).2)))
  let word := binSyms (A := A) H ((1-B) i j).val
  let E : Stacks T A := {D with R := Function.update D.R (r 3) word}
  obtain ⟨s,hs,copy⟩ := bcopy_exec body (a := r 3) (c := r 8) (t₁ := r 4) (t₂ := r 5)
    (by simp [List.nodup_cons,r.injective.eq_iff]) y E
    (by simp [E,D,r.injective.eq_iff,free 4 (by decide)]) (by simp [E,D,r.injective.eq_iff,free 5 (by decide)])
  let F : Stacks T A := {E with R := Function.update E.R (r 8) (word ++ S.R (r 8))}
  obtain ⟨z,hz,clear⟩ := clearWords_exec (body := body) [r 1,r 3] (by simp [r.injective.eq_iff]) s F
  simp [E,D,r.injective.eq_iff,word,length_binSyms] at copy
  simp [F,E,D,r.injective.eq_iff,word,length_binSyms] at clear
  refine ⟨z,_,hz.trans (hs.trans (hy.trans hu)),?_,(Exec.seq read (Exec.seq sub (Exec.seq copy clear))).cast rfl ?_⟩
  · omega
  · congr 1
    refine Stacks.ext ?_ ?_ ?_ ?_ <;> try rfl
    funext k
    by_cases h : k = r 1
    · subst k; simp [r.injective.eq_iff,free 1 (by decide)]
    by_cases g : k = r 3
    · subst k; simp [r.injective.eq_iff,free 3 (by decide)]
    by_cases o : k = r 8 <;> simp [o,g,h,r.injective.eq_iff]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
