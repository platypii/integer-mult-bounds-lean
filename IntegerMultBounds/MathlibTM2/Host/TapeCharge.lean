module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Additive tape costs under placement in a larger host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host

variable {T A : ℕ}

def tapeCharge {T A : ℕ} (weight : List (Fin (A+4)) → List (Fin (A+4)) → ℕ)
    (js : List (Fin T)) (S : Stacks T A) : ℕ :=
  (js.map fun j => weight (S.L j) (S.R j)).sum

/-- Transport a joint time and cleanup bound through tape placement. Tapes
outside the embedded bank contribute the same cost on entry and exit. -/
theorem placedCleanup_cost_le {M : ℕ} (place : Fin T ↪ Fin M) (S F : Stacks M A)
    (weight : List (Fin (A+4)) → List (Fin (A+4)) → ℕ) (time budget : ℕ)
    (frame : ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j)
    (localBill : ∀ is : List (Fin T), is.Nodup →
      time+tapeCharge weight is (embStk place F) ≤ tapeCharge weight is (embStk place S)+budget)
    (js : List (Fin M)) (distinct : js.Nodup) :
    time+tapeCharge weight js F ≤ tapeCharge weight js S+budget := by
  classical
  let cost := fun (D : Stacks M A) j => weight (D.L j) (D.R j)
  have split (ls : List (Fin M)) (unique : ls.Nodup) :
      ∃ (is : List (Fin T)) (outside : ℕ), is.Nodup ∧ (∀ i ∈ is, place i ∈ ls) ∧
        (ls.map (cost F)).sum = (is.map (cost F ∘ place)).sum+outside ∧
        (ls.map (cost S)).sum = (is.map (cost S ∘ place)).sum+outside := by
    induction ls with
    | nil => exact ⟨[],0,by simp,by simp,rfl,rfl⟩
    | cons j ls ih =>
      obtain ⟨is,b,nd,inside,final,initial⟩ := ih unique.tail
      by_cases hit : ∃ i, place i = j
      · obtain ⟨i,rfl⟩ := hit
        refine ⟨i::is,b,List.nodup_cons.mpr ⟨fun h => unique.notMem (inside i h),nd⟩,?_,?_,?_⟩
        · intro k hk
          rcases List.mem_cons.mp hk with rfl|hk
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (inside k hk)
        · simp [final,Nat.add_assoc]
        · simp [initial,Nat.add_assoc]
      · obtain ⟨left,right⟩ := frame j (fun i h => hit ⟨i,h⟩)
        have same : cost F j = cost S j := by simp [cost,left,right]
        refine ⟨is,cost S j+b,nd,fun i h => List.mem_cons_of_mem _ (inside i h),?_,?_⟩
        · simp [final,same,Nat.add_left_comm]
        · simp [initial,Nat.add_left_comm]
  obtain ⟨is,b,nd,_,final,initial⟩ := split js distinct
  have bill := localBill is nd
  change time+(is.map (cost F ∘ place)).sum ≤ (is.map (cost S ∘ place)).sum+budget at bill
  change time+(js.map (cost F)).sum ≤ (js.map (cost S)).sum+budget
  omega

end IntegerMultBounds.MathlibTM2.Host
