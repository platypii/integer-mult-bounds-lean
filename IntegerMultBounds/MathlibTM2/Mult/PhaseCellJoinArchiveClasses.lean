module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellJoinOwnedArchives

/-! Assemble finitely many isolated class archives using the existing verified
two-bank join. Every prefix rescan is charged; for the four publication classes
the resulting bill is linear in the total archive volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def joinArchiveClasses (src saved : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | bank::banks => .seq (joinOwnedArchives src bank saved) (joinArchiveClasses src saved banks)

theorem joinArchiveClasses_exec (src saved : Fin T) (hne : src ≠ saved)
    (banks : List (Fin T)) (hnodup : banks.Nodup)
    (hoff : ∀ bank ∈ banks, bank ≠ src ∧ bank ≠ saved)
    (X : List (Fin (A+4))) (data : Fin T → List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = X) (hsaved : S.R saved = []) (hbanks : ∀ bank ∈ banks, S.R bank = data bank) :
    ∃ v' F n, v'.user = v.user ∧
      n ≤ 4*banks.length*(X.length+(banks.flatMap data).length)+6*banks.length+1 ∧
      Exec body (joinArchiveClasses src saved banks) (mk v S) n (mk v' F) ∧
      F.R src = X++banks.flatMap data ∧ (∀ bank ∈ banks, F.R bank = []) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ i, i ≠ src → i ∉ banks → F.R i = S.R i := by
  induction banks generalizing X v S with
  | nil =>
    exact ⟨v,S,1,rfl,by simp,Exec.act _ _,by simpa using hsrc,by simp,rfl,rfl,rfl,fun _ _ _ => rfl⟩
  | cons bank banks ih =>
    have ho := hoff bank (by simp)
    have hn := List.nodup_cons.mp hnodup
    have hreg : [src,bank,saved].Nodup := by simp [hne,ho.1.symm,ho.2]
    obtain ⟨v₁,hu₁,he₁⟩ := joinOwnedArchives_exec (body := body) src bank saved hreg X (data bank) v S hsrc
      (hbanks bank (by simp)) hsaved
    let M : Stacks T A := {S with R := Function.update (Function.update S.R src (X++data bank)) bank []}
    obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hclear,hi,ho',hl,hframe⟩ := ih hn.2 (fun b hb => hoff b (by simp [hb]))
      (X++data bank) v₁ M (by simp [M,ho.1.symm]) (by simp [M,ho.2.symm,hne.symm,hsaved]) (by
        intro b hb
        have hbs := (hoff b (by simp [hb])).1
        have hbb : b ≠ bank := by intro he; subst b; exact hn.1 hb
        simpa [M,hbs,hbb] using hbanks b (by simp [hb]))
    refine ⟨v₂,F,(4*(X.length+(data bank).length)+6)+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,?_,?_,hi,ho',hl,?_⟩
    · simp only [List.length_append,List.flatMap_cons,List.length_cons] at hn₂ ⊢
      nlinarith only [hn₂,Nat.zero_le (banks.flatMap data).length]
    · simpa only [List.flatMap_cons,List.append_assoc] using hs
    · intro b hb
      rcases List.mem_cons.mp hb with he | hb
      · subst b
        rw [hframe bank ho.1 hn.1]; simp [M]
      · exact hclear b hb
    · intro i his hib
      have hib' : i ∉ banks := fun hi => hib (by simp [hi])
      have hibank : i ≠ bank := by intro he; subst i; exact hib (by simp)
      rw [hframe i his hib']
      simp [M,his,hibank]

theorem joinArchiveClasses_native (src saved : Fin T) (banks : List (Fin T)) :
    mnNativePushBound 1 (joinArchiveClasses (P := P) (Q := Q) (A := A) (U := U) src saved banks) := by
  induction banks with
  | nil => simp [joinArchiveClasses,mnNativePushBound,mnActPush]
  | cons bank banks ih => exact ⟨joinOwnedArchives_pushBound _ _ _,ih⟩

theorem joinArchiveClasses_within {src saved : Fin T} {banks : List (Fin T)}
    {v v' : HS T Q A U} {S F : Stacks T A} {n volume : ℕ}
    (he : Exec body (joinArchiveClasses src saved banks) (mk v S) n (mk v' F))
    (hn : n ≤ 4*banks.length*volume+6*banks.length+1) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+4*banks.length*volume+6*banks.length+1) depth
      (joinArchiveClasses src saved banks) (mk v S) n (mk v' F) := by
  exact mn_native_exec_within he 1 (joinArchiveClasses_native src saved banks) depth _ (by omega)

/-- Joining the other three banks into the first of four class archives has a
linear bound, including all prefix rescans and the final stop. -/
theorem joinArchiveClasses_four_cost_le (banks : List (Fin T)) (hcount : banks.length ≤ 3) (volume : ℕ) :
    4*banks.length*volume+6*banks.length+1 ≤ 12*volume+19 := by
  have hv := Nat.mul_le_mul_right volume (Nat.mul_le_mul_left 4 hcount)
  have hc := Nat.mul_le_mul_left 6 hcount
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
