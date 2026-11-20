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

/-- Release the frame moduli in reverse initialization order. -/
def clearFrames (pool : Fin ((D+1)*13) ↪ Fin T) : ℕ → Pr P T Q A U
  | 0 => .act .done
  | n+1 => .seq (bclear (frame pool n 2)) (clearFrames pool n)

theorem clearFrames_exec (body : P → Pr P T Q A U) (pool : Fin ((D+1)*13) ↪ Fin T)
    (H : ℕ) (original : Regs T A) (n : ℕ) (fits : n ≤ D+1) (v : HS T Q A U) (S : Stacks T A)
    (width : ∀ k < n, (S.R (frame pool k 2)).length = H)
    (blank : ∀ k < n, original (frame pool k 2) = [])
    (keep : ∀ i, (∀ k < n, i ≠ frame pool k 2) → S.R i = original i) :
    ∃ z, z.user = v.user ∧ Exec body (clearFrames pool n) (mk v S)
      (n*(2*H+2)+1) (mk z {S with R := original}) := by
  induction n generalizing S v with
  | zero =>
    have same : S.R = original := funext fun i => keep i (by simp)
    exact ⟨v,rfl,by simpa [clearFrames,← same,Action.run] using Exec.act (body := body) .done (mk v S)⟩
  | succ n ih =>
    obtain ⟨u,hu,_,clear⟩ := bclear_exec body (frame pool n 2) v S
    let B := {S with R := Function.update S.R (frame pool n 2) []}
    have away (k) (hk : k < n) : B.R (frame pool k 2) = S.R (frame pool k 2) :=
      Function.update_of_ne (separate pool hk (by omega) 2 2).symm _ _
    obtain ⟨z,hz,run⟩ := ih (by omega) u B
      (fun k hk => (congrArg List.length (away k hk)).trans (width k (by omega)))
      (fun k hk => blank k (by omega)) (by
        intro i outside
        by_cases eq : i = frame pool n 2
        · subst i; simp [B,blank n (by omega)]
        · exact (Function.update_of_ne eq _ _).trans (keep i (fun k hk => by
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h | rfl
            · exact outside k h
            · exact eq)))
    rw [width n (by omega)] at clear
    refine ⟨z,hz.trans hu,?_⟩
    simpa only [clearFrames,Nat.succ_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
      using Exec.seq clear run

/-- A writer may borrow a blank formula pool and return it blank, preserving
its ordinary single-output tape contract. -/
theorem withFrames_exec (body : P → Pr P T Q A U) (pool : Fin ((D+1)*13) ↪ Fin T)
    (src dst : Fin T) (sourceOff : ∀ j, src ≠ pool j) (destOff : ∀ j, dst ≠ pool j)
    (program : Pr P T Q A U) (word : List (Fin (A+4))) (cost : ℕ)
    (u : HS T Q A U) (S : Stacks T A) (blank : ∀ j, S.R (pool j) = [])
    (writer : ∀ (v : HS T Q A U) (B : Stacks T A),
      (∀ i, (∀ j, i ≠ pool j) → B.R i = S.R i) →
      (∀ k ≤ D, B.R (frame pool k 2) = S.R src) →
      (∀ k ≤ D, ∀ i : Fin 13, i ≠ 2 → B.R (frame pool k i) = []) →
      ∃ z n, z.user = v.user ∧ n ≤ cost ∧ Exec body program (mk v B) n
        (mk z {B with R := Function.update B.R dst (word ++ B.R dst)})) :
    ∃ z t, z.user = u.user ∧ t ≤ (D+1)*(6*(S.R src).length+6)+1 + (cost+((D+1)*(2*(S.R src).length+2)+1)) ∧
      Exec body ((initFrames pool src (D+1)).seq (program.seq (clearFrames pool (D+1)))) (mk u S) t
        (mk z {S with R := Function.update S.R dst (word ++ S.R dst)}) := by
  obtain ⟨v,B,hv,init,inp,out,left,filled,keep⟩ := initFrames_exec body pool src sourceOff u S blank (D+1) le_rfl
  have external (i) (h : ∀ j, i ≠ pool j) := keep i (fun _ _ => h _)
  obtain ⟨y,n,hy,hn,run⟩ := writer v B external (fun k hk => filled k (by omega)) (by
    intro k hk i hi
    apply Eq.trans (keep _ _) (blank _)
    intro l hl
    rcases lt_trichotomy l k with h | rfl | h
    · exact separate pool h hk i 2
    · exact (frame pool l).injective.ne hi
    · exact (separate pool h (by omega) 2 i).symm)
  let E := {B with R := Function.update B.R dst (word ++ B.R dst)}
  let original := Function.update S.R dst (word ++ S.R dst)
  have off (k) : frame pool k 2 ≠ dst := (destOff _).symm
  obtain ⟨z,hz,clear⟩ := clearFrames_exec body pool (S.R src).length original (D+1) le_rfl y E
    (fun k hk => by simp [E,off,filled k hk])
    (fun k _ => (Function.update_of_ne (off k) _ _).trans (blank _))
    (by intro i hi
        by_cases eq : i = dst
        · subst i; simp [E,original,external dst destOff]
        · simp [E,original,eq,keep i hi])
  refine ⟨z,_,hz.trans (hy.trans hv),Nat.add_le_add_left (Nat.add_le_add_right hn _) _,Exec.seq init (Exec.seq run ?_)⟩
  simpa only [E,inp,out,left,original] using clear

end IntegerMultBounds.MathlibTM2.Cover.Fallback.RingFormula
