module

public import IntegerMultBounds.MathlibTM2.Fast.SynBase
public import IntegerMultBounds.MathlibTM2.M6.BitPackedPhysicalStage

/-! Park aligned PR589 owner words on one reusable archive tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Fast

private theorem ownerStashCost {T A : ℕ} (regs : Fin T → List (Fin (A+4)))
    (xs : List (Fin T)) (V : ℕ) (width : ∀ i ∈ xs, (regs i).length = V) :
    synStashCost regs xs = xs.length*(2*V+3)+1 := by
  induction xs with
  | nil => simp [synStashCost]
  | cons i xs ih =>
    rw [synStashCost,width i List.mem_cons_self,ih (fun j hj => width j (List.mem_cons_of_mem i hj))]
    simp only [List.length_cons,Nat.add_mul,one_mul]
    omega

/-- A child can use every parked owner tape provided it returns them empty.
Other registers may change, and an older archive frame survives the call. -/
theorem runWithParkedOwners {T Q A V : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (call : Pr P T Q A U) (archive : Fin T) (xs : List (Fin T)) (distinct : xs.Nodup)
    (off : archive ∉ xs) (R F : Fin T → List (Fin (A+4)))
    (words : ∀ i ∈ xs, ∃ data : Fin V → ZMod 2, R i = List.ofFn (fun j => SparseRoleCircuit.encode (data j)))
    (restore : ∀ i ∈ xs, F i = R i) (tail : F archive = R archive) (price : ℕ)
    (child : LayRuns body call
      (Function.update (synClr R xs) archive (synStk R separator xs ++ separator :: R archive))
      (Function.update (synClr F xs) archive (synStk R separator xs ++ separator :: R archive)) price) :
    LayRuns body ((synStash archive separator xs).seq (call.seq (synUnstash archive separator xs)))
      R F (price+2*(xs.length*(2*V+3)+2)) := by
  have safe (i) (hi : i ∈ xs) : separator ∉ F i := by
    obtain ⟨data,word⟩ := words i hi
    rw [restore i hi,word,List.mem_ofFn]
    rintro ⟨j,eq⟩
    unfold SparseRoleCircuit.encode at eq
    cases h : decide (data j = 1) <;> simp [h,bitSymbol,separator,Fin.ext_iff] at eq
  have back := lr_synUnstash body (R := F) separator xs (R archive) distinct off safe
  rw [synStk_congr separator xs restore,← tail,Function.update_eq_self] at back
  have run := (lr_synStash body (R := R) separator xs distinct off).seq (child.seq (by simpa only [tail] using back))
  apply lr_weaken body run rfl
  have width i (hi : i ∈ xs) : (R i).length = V := by
    obtain ⟨_,word⟩ := words i hi
    rw [word,List.length_ofFn]
  rw [ownerStashCost R xs V width,ownerStashCost F xs V (fun i hi => restore i hi ▸ width i hi)]
  omega

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- Park any selected set of the actual parent-stage owners. The per-owner
bill uses the represented word length, independently of the two control tapes. -/
theorem ParentStageWords.park {T Q V : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (call : Pr P T Q prime U) (fan : Fin (142081+2) ↪ Fin T) (archive : Fin T)
    (owners : List (Fin 142081)) (distinct : owners.Nodup)
    (data : Fin 142081 → Fin V → ZMod 2) (S : Stacks T prime)
    (words : ParentStageWords (fun i => fan (i.castAdd 2)) fan V data S)
    (F : Fin T → List (Fin (prime+4))) (price : ℕ) :
    let port := (Fin.castAddEmb 2 (n := 142081)).trans fan
    let xs := owners.map port
    archive ∉ xs → (∀ i ∈ owners, F (port i) = S.R (port i)) → F archive = S.R archive →
    LayRuns body call
      (Function.update (synClr S.R xs) archive (synStk S.R separator xs ++ separator :: S.R archive))
      (Function.update (synClr F xs) archive (synStk S.R separator xs ++ separator :: S.R archive)) price →
    LayRuns body ((synStash archive separator xs).seq (call.seq (synUnstash archive separator xs)))
      S.R F (price+2*(owners.length*(2*V+3)+2)) := by
  intro port xs off restored tail child
  have len : xs.length = owners.length := List.length_map _
  rw [← len]
  apply runWithParkedOwners body call archive xs (distinct.map port.injective) off S.R F _ _ tail price child
  · rintro _ hi
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hi
    exact ⟨data i,words.right i⟩
  · rintro _ hi
    obtain ⟨i,mem,rfl⟩ := List.mem_map.mp hi
    exact restored i mem

end IntegerMultBounds.MathlibTM2.M6.BitNode
