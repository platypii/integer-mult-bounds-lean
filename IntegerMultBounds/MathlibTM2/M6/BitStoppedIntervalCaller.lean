module

public import IntegerMultBounds.MathlibTM2.M6.BitStoppedRowEntry
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactRead

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Run the stopped interval in the caller's workspace. Its result is indexed by the
scheduled child, and every tape outside the placement retains both stacks. -/
theorem placedStoppedInterval [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    ∃ (C : ℝ) (N : ℕ) (table : Unit → Pr Unit N Q prime U) (worker : Pr Unit N Q prime U)
      (port : Fin N) (master : Fin 6 ↪ Fin N), 0 ≤ C ∧ (∀ i, master i ≠ port) ∧
    ∀ {P : Type} {T : ℕ} (body : P → Pr P T Q prime U) (place : Fin N ↪ Fin T) (entry : Unit → P),
      (∀ f, body (entry f) = embProg place entry (table f)) →
    ∀ (src tmp : Fin T), [src,tmp,place port].Nodup →
    ∀ (lane child : Descriptor), let wide := {lane with afterD := lane.afterD*142080}
      ∀ (position : Fin (volume prime child) ≃ Fin (volume prime wide)),
      InheritedIntervalPositions child wide rfl position → lane.width = child.width →
      0 < volume prime lane → 0 < lane.width → ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      RecordPayload src (fun _ => blank) 0 word S → S.L tmp = [] → S.R tmp = [] → S.R (place port) = [] →
      (∀ i, S.R (place (master i)) = (Routines.hdr lane i).map bitSymbol) →
      (∀ j, S.L (place j) = []) → (∀ j, j ≠ port → (∀ i, master i ≠ j) → S.R (place j) = []) →
      ∃ z F t changed, Exec body ((loadCompactWord src tmp (place port)).seq (embProg place entry worker)) (mk u S) t (mk z F) ∧
        t ≤ 8*volume prime child+10+⌊(C*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊ ∧
        z.user = u.user ∧ RecordPayload (place port) (fun _ => blank) 0 changed F ∧
        (∀ j, changed (position j) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) j) ∧
        (∀ j, j ≠ port → F.L (place j) = [] ∧ F.R (place j) = []) ∧
        ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨C,N,table,worker,port,master,pos,apart,run⟩ := cleanStoppedInterval (U := U) capacity mergeCap
  refine ⟨C,N,table,worker,port,master,pos,apart,?_⟩
  intro P T body place entry dispatch src tmp distinct lane child wide position coords width positive live word u S source tl tr fresh headers left blank
  have size : volume prime lane*142080 = volume prime wide := by simp [wide,volume,Nat.mul_assoc]
  have mass := Fintype.card_congr position
  simp only [Fintype.card_fin] at mass
  have reads : WordAtZero word (S.L src) (S.R src) := by
    intro j
    rw [← encodedOwnerCell]
    simpa only [sub_zero,List.map_ofFn] using source j
  obtain ⟨a,initial,load⟩ := loadCompactWord_exec body src tmp (place port) distinct word u S reads tl tr
  simp only [fresh,List.append_nil] at load
  let E := {S with R := Function.update S.R (place port) (List.ofFn fun i => SparseRoleCircuit.encode (word i))}
  have input : E.R (place port) = _ := (Function.update_self ..).trans (List.ofFn_congr size.symm _)
  have off (j) (ne : j ≠ place port) : E.R j = S.R j := Function.update_of_ne ne ..
  obtain ⟨v,D,t,ran,paid,user,read,clean⟩ := run lane positive live word (embDn place a) (embStk place E)
    input (fun i => (off _ (place.injective.ne (apart i))).trans (headers i)) left
    (fun j away h => (off _ (place.injective.ne away)).trans (blank j away h))
  obtain ⟨z,F,exec,_,same,eq,frame⟩ := exec_emb place.injective dispatch ran a rfl E rfl
  rw [← eq] at read clean
  refine ⟨z,F,_,_,load.seq exec,?_,same.trans (user.trans initial),read,(coords.transpose_iff width word _).2 rfl,clean,?_⟩
  · rw [mass]
    exact Nat.add_le_add_left (by simpa only [width,size] using paid) _
  · intro j away
    exact ⟨(frame j away).1,(frame j away).2.trans (off j (away port).symm)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
