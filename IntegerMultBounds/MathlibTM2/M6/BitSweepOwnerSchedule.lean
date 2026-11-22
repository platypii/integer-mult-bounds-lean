module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepNodeAddress
public import IntegerMultBounds.MathlibTM2.Cover.LabelTraversal

/-! Compose restoring, single-owner conversions over the full PR589 role bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Shared50ModularControl Stack Host Node Cover.LabelTraversal

noncomputable def sweepRoleTape : Role ↪ Fin 142081 :=
  ((Fintype.equivFin Role).trans (finCongr card_role)).toEmbedding.trans Fin.castSuccEmb

theorem sweepRoleTape_eq (r : Role) : sweepRoleTape r = bankTape r.bank (r.replica,r.port,r.cls) := rfl

private theorem distinctTapeSequence {ι P U : Type} {T Q A : ℕ} (body : P → Pr P T Q A U)
    (tape : ι ↪ Fin T) (code : ι → Pr P T Q A U) (xs : List ι) (unique : xs.Nodup)
    (input output : ι → List (Fin (A+4))) (cost : ι → ℕ) (u : HS T Q A U) (S : Stacks T A)
    (start : ∀ i, S.R (tape i) = input i)
    (step : ∀ i (v : HS T Q A U) (F : Stacks T A), F.R (tape i) = input i →
      (∀ j, (∀ a, tape a ≠ j) → F.R j = S.R j) →
      ∃ y l, y.user = v.user ∧ l ≤ cost i ∧ Exec body (code i) (mk v F) l
        (mk y {F with R := Function.update F.R (tape i) (output i)})) :
    ∃ z R t, z.user = u.user ∧ t ≤ (xs.map cost).sum+1 ∧ Exec body (sequence code xs) (mk u S) t (mk z {S with R := R}) ∧
      (∀ i ∈ xs, R (tape i) = output i) ∧ ∀ j, (∀ i ∈ xs, tape i ≠ j) → R j = S.R j := by
  induction xs with
  | nil => exact ⟨u,S.R,1,rfl,by simp,Exec.act _ _,by simp,by simp⟩
  | cons i xs ih =>
    obtain ⟨absent,nd⟩ := List.nodup_cons.mp unique
    obtain ⟨v,R,k,hv,hk,prev,done,frame⟩ := ih nd
    have original := (frame (tape i) (fun j hj => tape.injective.ne (fun eqn => absent (eqn ▸ hj)))).trans (start i)
    obtain ⟨y,l,hy,hl,run⟩ := step i v {S with R := R} original (fun j hj => frame j (fun a _ => hj a))
    refine ⟨y,_,_,hy.trans hv,by simp only [List.map_cons,List.sum_cons]; omega,Exec.seq prev run,?_,?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Function.update_self ..
      · have distinct : j ≠ i := fun eqn => absent (eqn ▸ hj)
        exact (Function.update_of_ne (tape.injective.ne distinct) _ _).trans (done j hj)
    · intro j hj
      exact (Function.update_of_ne (hj i (by simp)).symm _ _).trans (frame j (fun a ha => hj a (List.mem_cons_of_mem _ ha)))

/-- Each role is visited exactly once. The permanent extra owner tape and
the enclosing workspace retain their original contents. -/
theorem sweepOwnerSchedule_exec {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (owners : Fin 142081 ↪ Fin T) (code : Role → Pr P T Q prime U) :
    ∃ program : Pr P T Q prime U, ∀ (input output : Role → List (Fin (prime+4))) (C volume : ℕ)
      (u : HS T Q prime U) (S : Stacks T prime),
    let tape := sweepRoleTape.trans owners
    (∀ r, S.R (tape r) = input r) →
    (∀ r (v : HS T Q prime U) (F : Stacks T prime), F.R (tape r) = input r →
      (∀ j, (∀ a, tape a ≠ j) → F.R j = S.R j) →
      ∃ y l, y.user = v.user ∧ l ≤ C*volume+8 ∧ Exec body (code r) (mk v F) l
        (mk y {F with R := Function.update F.R (tape r) (output r)})) →
    ∃ z R t, z.user = u.user ∧ t ≤ 142080*(C*volume+8)+1 ∧ Exec body program (mk u S) t (mk z {S with R := R}) ∧
      (∀ r, R (tape r) = output r) ∧ ∀ j, (∀ r, tape r ≠ j) → R j = S.R j := by
  classical
  let e := Fintype.equivFin Role
  let roles := (List.finRange (Fintype.card Role)).map e.symm
  refine ⟨sequence code roles,?_⟩
  intro input output C volume u S tape start step
  have nd : roles.Nodup := (List.nodup_finRange _).map e.symm.injective
  have allRoles (r : Role) : r ∈ roles := List.mem_map.mpr ⟨e r,List.mem_finRange _,e.symm_apply_apply _⟩
  obtain ⟨z,R,t,hz,ht,run,done,frame⟩ := distinctTapeSequence body tape code roles nd input output
    (fun _ => C*volume+8) u S start step
  exact ⟨z,R,t,hz,by simpa only [List.map_const',List.sum_replicate_nat,roles,List.length_map,List.length_finRange,card_role] using ht,run,fun r => done r (allRoles r),fun j hj => frame j (fun r _ => hj r)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
