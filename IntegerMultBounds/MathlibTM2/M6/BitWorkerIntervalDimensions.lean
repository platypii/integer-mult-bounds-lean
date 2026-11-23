module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalPackEntry
public import IntegerMultBounds.MathlibTM2.M6.BitParkedPackedChild

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)

/-- Prepare the row packer's dimensions on private tapes from the caller's four
right stacks. The caller may keep arbitrary data to the left of each head. -/
theorem prepareWorkerIntervalDimensions {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (caller work : Fin 72 ↪ Fin T) (apart : ∀ i j, work i ≠ caller j) :
    ∃ code : Pr P T Q prime U, ∀ w W (v : HS T Q prime U) (S : Stacks T prime),
      let M := prime^(w+1)
      S.R (caller 2) = binSyms M.size M → S.R (caller 53) = binSyms W.size W →
      S.R (caller 28) = binSyms 1 1 → (S.R (caller 71)).length = w+1 →
      (∀ j, S.L (work j) = [] ∧ S.R (work j) = []) →
      ∃ z F n, Exec body code (mk v S) n (mk z F) ∧ z.user = v.user ∧
        n ≤ 6*(M.size+W.size)+27*(w+1)+44 ∧
        IntervalHeaderInputs (intervalDirectoryPorts.trans work) (work 59) w W F ∧
        ∀ j, (∀ i, work i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  let operands : Fin 4 ↪ Fin 72 := ⟨![2,53,28,71],by decide⟩
  let source := operands.trans caller
  let dest := operands.trans work
  obtain ⟨load,copy⟩ := reloadChildSeed body dest source (work 60) (work 61)
    (fun i j => apart _ _) (by
      intro i
      have h : ∀ i : Fin 4, operands i ≠ 60 ∧ operands i ≠ 61 := by decide
      simp [source,dest,Function.Embedding.trans_apply,Ne.symm (apart (operands i) (operands i)),
        Ne.symm (apart 60 (operands i)),Ne.symm (apart 61 (operands i)),work.injective.eq_iff,h i])
  obtain ⟨prepare,run⟩ := intervalDirectorySetup_exec body work
  refine ⟨load.seq prepare,?_⟩
  intro w W v S M base suffix unit atom fresh
  let seed := fun i => S.R (source i)
  obtain ⟨a,R,k,setup,paid,initial,loaded,off⟩ := copy seed v S (fun _ => rfl)
    (fun i => (fresh _).2) (fresh 60).2 (fresh 61).2
  have empty (j : Fin 72) (lo : 59 ≤ j.val) (hi : j.val ≤ 65) : R (work j) = [] := by
    apply (off _ ?_).trans (fresh j).2
    intro i
    exact work.injective.ne ((by decide : ∀ j : Fin 72, 59 ≤ j.val → j.val ≤ 65 → ∀ i, operands i ≠ j) j lo hi i)
  obtain ⟨z,F,n,exec,time,user,inputs,left,right⟩ := run w W a {S with R := R}
    ((loaded 0).trans base) ((loaded 1).trans suffix) ((loaded 2).trans unit)
    (fun i => (fresh _).1) ((congrArg List.length (loaded 3)).trans atom) empty
  refine ⟨z,F,_,setup.seq exec,user.trans initial,?_,inputs,?_⟩
  · rw [show List.finRange 4 = [0,1,2,3] by decide] at paid
    change  k ≤ (6*(S.R (caller 2)).length+6)+((6*(S.R (caller 53)).length+6)+
      ((6*(S.R (caller 28)).length+6)+((6*(S.R (caller 71)).length+6)+0)))+1 at paid
    simp only [base,suffix,unit,length_binSyms,atom] at paid
    omega
  · intro j away
    exact ⟨left j (fun i => away _),(right j (away 59)).trans (off j (fun i => away _))⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
