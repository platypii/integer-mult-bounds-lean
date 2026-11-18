module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackStreamedItinerary

/-! Visit the saved elimination stages in reverse and recover both original stacks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Node
variable {T Q A : ℕ} {P U : Type}

theorem length_matrixWords {M d : ℕ} [NeZero M] (A H : ℕ) (m : Matrix (Fin d) (Fin d) (ZMod M)) :
    (matrixWords A H m).length = d*d*H := by
  simp [matrixWords,List.length_flatten,List.map_ofFn,Function.comp_def,length_binSyms,List.ofFn_const,Nat.mul_assoc]

private theorem archive_top (stage : ℕ → List α) (tail dest : List α) (n : ℕ) :
    ∃ suffix, (matrixArchive stage (stage 0 ++ tail) dest n).1 = stage n ++ suffix := by
  cases n <;> exact ⟨_,rfl⟩

/-- Drop fixed-width words using the live modulus as the width register. -/
def dropWords (width src tmp : Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | k+1 => .seq (usub width src tmp) (dropWords width src tmp k)

theorem dropWords_exec (body : P → Pr P T Q A U) {width src tmp : Fin T}
    (ws : width ≠ src) (wt : width ≠ tmp) (st : src ≠ tmp) (k H : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (len : (S.R width).length = H) (blank : S.R tmp = []) :
    ∃ z, z.user = v.user ∧ Exec body (dropWords width src tmp k) (mk v S) (k*(4*H+4)+1)
      (mk z {S with R := Function.update S.R src ((S.R src).drop (k*H))}) := by
  induction k generalizing v S with
  | zero => exact ⟨v,rfl,by simpa [dropWords] using Exec.act (body := body) .done (mk v S)⟩
  | succ k ih =>
    obtain ⟨u,hu,drop⟩ := usub_exec body ws wt st v S blank
    rw [len] at drop
    let D : Stacks T A := {S with R := Function.update S.R src ((S.R src).drop H)}
    obtain ⟨z,hz,rest⟩ := ih u D (by simpa [D,ws] using len) (by simpa [D,st.symm] using blank)
    refine ⟨z,hz.trans hu,(Exec.seq drop rest).cast (by rw [Nat.succ_mul k]; omega) ?_⟩
    simp [D,List.drop_drop,Nat.succ_mul,Nat.add_comm]

/-- The preceding matrix is already on the opposite stack. After its callback, discard the
newer matrix and exchange roles for the next step. -/
def rewind (words : ℕ) (visit : ℕ → Fin T → Pr P T Q A U) (count tmp : Fin T) :
    ℕ → Fin T → Fin T → Pr P T Q A U
  | 0, _, _ => .act .done
  | n+1, active, other => .seq (visit n other) (.seq (dropWords count active tmp words) (rewind words visit count tmp n other active))

/-- Callers can use payload registers freely. The callback preserves the four registers
needed for the traversal and advances its own invariant by one reverse stage. -/
theorem rewind_exec (body : P → Pr P T Q A U) (visit : ℕ → Fin T → Pr P T Q A U)
    (count tmp : Fin T) (ct : count ≠ tmp) (stage : ℕ → List (Fin (A+4))) (words H : ℕ)
    (width : ∀ j, (stage j).length = words*H) (tail dest : List (Fin (A+4)))
    (ok : ℕ → Stacks T A → Prop) (cost : ℕ)
    (step : ∀ j src dst (v : HS T Q A U) (S : Stacks T A),
      [count,tmp,src,dst].Nodup → ok (j+1) S →
      (∃ suffix, S.R src = stage j ++ suffix) →
      ∃ z F l, z.user = v.user ∧ l ≤ cost ∧ Exec body (visit j src) (mk v S) l (mk z F) ∧
        F.R src = S.R src ∧ F.R dst = S.R dst ∧ F.R count = S.R count ∧ F.R tmp = S.R tmp ∧
        ok j {F with R := Function.update F.R dst ((F.R dst).drop (words*H))})
    (n : ℕ) (active other : Fin T) (regs : [count,tmp,other,active].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (ready : ok n S)
    (packed : (S.R active,S.R other) = matrixArchive stage (stage 0 ++ tail) dest n)
    (len : (S.R count).length = H) (blank : S.R tmp = []) :
    ∃ z F l, z.user = v.user ∧ l ≤ n*(cost+(words*(4*H+4)+1))+1 ∧ Exec body (rewind words visit count tmp n active other) (mk v S) l (mk z F) ∧
      ok 0 F ∧ (if n % 2 = 0 then (F.R active,F.R other) else (F.R other,F.R active)) = (stage 0 ++ tail,dest) := by
  induction n generalizing active other v S with
  | zero => exact ⟨v,S,1,rfl,by simp,Exec.act (body := body) .done _,ready,by simpa [matrixArchive] using packed⟩
  | succ n ih =>
    have older := congrArg Prod.snd packed
    have newer := congrArg Prod.fst packed
    simp only [matrixArchive] at older newer
    obtain ⟨suffix,top⟩ := archive_top stage tail dest n
    obtain ⟨u,F,l,hu,hl,run,hs,hd,hc,ht,next⟩ := step n other active v S regs ready ⟨suffix,older.trans top⟩
    have hr := regs
    regs_ne hr
    obtain ⟨y,hy,drop⟩ := dropWords_exec body ‹count ≠ active› ct ‹tmp ≠ active›.symm words H u F
      (by rw [hc,len]) (ht.trans blank)
    let D : Stacks T A := {F with R := Function.update F.R active ((F.R active).drop (words*H))}
    have keep (i : Fin T) (h : i ≠ active) : D.R i = F.R i := Function.update_of_ne h _ _
    have pair : (D.R other,D.R active) = matrixArchive stage (stage 0 ++ tail) dest n := by
      apply Prod.ext
      · exact (keep other ‹other ≠ active›).trans (hs.trans older)
      · change Function.update F.R active _ active = _
        rw [Function.update_self,hd,newer,← width (n+1),List.drop_left]
    obtain ⟨z,G,t,hz,hcost,rec,okG,endG⟩ := ih other active (by regs_nodup) y D next pair
      (by rw [keep count ‹count ≠ active›,hc,len]) ((keep tmp ‹tmp ≠ active›).trans (ht.trans blank))
    refine ⟨z,G,l+((words*(4*H+4)+1)+t),hz.trans (hy.trans hu),?_,Exec.seq run (Exec.seq drop rec),okG,?_⟩
    · rw [Nat.succ_mul n]; omega
    · by_cases h : n%2 = 0
      · simpa [h,show (n+1)%2 ≠ 0 by omega] using endG
      · simpa [h,show (n+1)%2 = 0 by omega] using endG

end IntegerMultBounds.MathlibTM2.Cover.Fallback
