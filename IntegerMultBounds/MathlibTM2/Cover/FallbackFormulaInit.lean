module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackFormulaLayout

/-! Copy the live modulus into the arithmetic frame at each formula depth. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal Node
variable {T D Q A : ℕ} {P U : Type}

def initFrames (pool : Fin ((D+1)*13) ↪ Fin T) (src : Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | n+1 => .seq (initFrames pool src n) (bcopy src (frame pool n 2) (frame pool n 0) (frame pool n 1))

theorem initFrames_exec (body : P → Pr P T Q A U) (pool : Fin ((D+1)*13) ↪ Fin T) (src : Fin T)
    (outside : ∀ j, src ≠ pool j) (v : HS T Q A U) (S : Stacks T A)
    (blank : ∀ j, S.R (pool j) = []) (n : ℕ) (fits : n ≤ D+1) :
    ∃ z F, z.user = v.user ∧ Exec body (initFrames pool src n) (mk v S)
      (n*(6*(S.R src).length+6)+1) (mk z F) ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      (∀ k < n, F.R (frame pool k 2) = S.R src) ∧
      ∀ i, (∀ k < n, i ≠ frame pool k 2) → F.R i = S.R i := by
  induction n with
  | zero => exact ⟨v,S,rfl,by simpa [initFrames,Action.run] using Exec.act (body := body) .done (mk v S),
      rfl,rfl,rfl,by simp,fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨u,B,hu,run,inp,out,left,filled,keep⟩ := ih (by omega)
    have same (i : Fin 13) : B.R (frame pool n i) = [] :=
      (keep _ (fun k hk => separate pool hk (by omega) i 2)).trans (blank _)
    have srcEq := keep src (fun _ _ => outside _)
    have ports : [src,frame pool n 2,frame pool n 0,frame pool n 1].Nodup := by
      simp [(frame pool n).injective.eq_iff,show ∀ i, src ≠ frame pool n i from fun _ => outside _]
    obtain ⟨z,hz,copy⟩ := bcopy_exec body ports u B (same 0) (same 1)
    rw [same 2,List.append_nil,srcEq] at copy
    refine ⟨z,{B with R := Function.update B.R (frame pool n 2) (S.R src)},hz.trans hu,?_,inp,out,left,?_,?_⟩
    · simpa only [initFrames,Nat.succ_mul,Nat.add_right_comm] using Exec.seq run copy
    · intro k hk
      by_cases eq : k = n
      · subst k; simp
      exact (Function.update_of_ne (separate pool (by omega : k < n) (by omega) 2 2).symm _ _).trans (filled k (by omega))
    · intro i hi
      exact (Function.update_of_ne (hi n (by omega)) _ _).trans (keep i (fun k hk => hi k (by omega)))

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
