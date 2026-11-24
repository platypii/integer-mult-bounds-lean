module

public import IntegerMultBounds.MathlibTM2.Fast.SynBase
public import IntegerMultBounds.MathlibTM2.Host.StackFrame
public import IntegerMultBounds.MathlibTM2.M6.BitPackedStageHandoff

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

private theorem stashUsesRight {P U : Type} {T Q A : ℕ} (archive : Fin T)
    (marker : Fin (A+4)) (xs : List (Fin T)) :
    programOn nonLeft (synStash archive marker xs : Pr P T Q A U) ∧
    programOn nonLeft (synUnstash archive marker xs : Pr P T Q A U) := by
  have parts : programOn nonLeft (synStashL archive marker xs : Pr P T Q A U) ∧
      programOn nonLeft (synUnstashL archive marker xs : Pr P T Q A U) := by
    induction xs with
    | nil => exact ⟨True.intro,True.intro⟩
    | cons x xs ih =>
      simpa [synStashL,synUnstashL,synPush,synPop,synMoveUntil,synPeekNe,synMvStep,
        moveR,whileR,moveStep,peekR,programOn,actionOn,nonLeft] using ih
  exact ⟨⟨by trivial,parts.1⟩,⟨parts.2,by trivial⟩⟩

private theorem runRight {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
    {p : Pr P T Q A U} {R F : Fin T → List (Fin (A+4))} {price : ℕ}
    (run : LayRuns body p R F price) (right : programOn nonLeft p)
    (u : HS T Q A U) (S : Stacks T A) (words : S.R = R) :
    ∃ z n, z.user = u.user ∧ n ≤ price ∧ Exec body p (mk u S) n (mk z {S with R := F}) := by
  obtain ⟨z,n,user,paid,exec⟩ := run u {S with L := fun _ => []} (fun _ => rfl) words
  exact ⟨z,n,user,paid,exec_withLeft exec right S.L⟩

theorem stashRight_exec {P U : Type} {T Q A : ℕ} (body : P → Pr P T Q A U)
    (archive : Fin T) (marker : Fin (A+4)) (xs : List (Fin T)) (nd : xs.Nodup)
    (off : archive ∉ xs) (u : HS T Q A U) (S : Stacks T A) :
    ∃ z n, z.user = u.user ∧ n ≤ synStashCost S.R xs+1 ∧ Exec body (synStash archive marker xs) (mk u S) n
      (mk z {S with R := Function.update (synClr S.R xs) archive (synStk S.R marker xs ++ marker :: S.R archive)}) :=
  runRight (lr_synStash body marker xs nd off) (stashUsesRight archive marker xs).1 u S rfl

theorem unstashRight_exec {P U : Type} {T Q A : ℕ} (body : P → Pr P T Q A U)
    (archive : Fin T) (marker : Fin (A+4)) (xs : List (Fin T)) (nd : xs.Nodup)
    (off : archive ∉ xs) (R : Fin T → List (Fin (A+4))) (tail : List (Fin (A+4)))
    (safe : ∀ j ∈ xs, marker ∉ R j) (u : HS T Q A U) (S : Stacks T A)
    (start : S.R = Function.update (synClr R xs) archive (synStk R marker xs ++ marker :: tail)) :
    ∃ z n, z.user = u.user ∧ n ≤ synStashCost R xs+1 ∧ Exec body (synUnstash archive marker xs) (mk u S) n
      (mk z {S with R := Function.update R archive tail}) :=
  runRight (lr_synUnstash body marker xs tail nd off safe) (stashUsesRight archive marker xs).2 u S start

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

open IntegerMultBounds.Networks.Shared50ModularControl (prime) in
/-- Save and restore owner words around an actual child execution. The caller's
left stacks survive parking. Clear the borrowed tapes before restoring the parent. -/
theorem ParentStageWords.park_exec {T Q V : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (call : Pr P T Q prime U) (fan : Fin (142081+2) ↪ Fin T) (archive : Fin T)
    (owners : List (Fin 142081)) (distinct : owners.Nodup)
    (data : Fin 142081 → Fin V → ZMod 2) (S : Stacks T prime)
    (words : ParentStageWords (fun i => fan (i.castAdd 2)) fan V data S)
    (price : ℕ) (u : HS T Q prime U)
    (result : Stacks T prime → Prop) :
    let port := (Fin.castAddEmb 2 (n := 142081)).trans fan
    let xs := owners.map port
    let park := fun R => Function.update (synClr R xs) archive (synStk S.R separator xs ++ separator :: S.R archive)
    archive ∉ xs →
    (∀ v : HS T Q prime U, v.user = u.user → (∀ j ∈ xs, S.L j = [] ∧ park S.R j = []) → ∃ z G n,
      Exec body call (Host.mk v {S with R := park S.R}) n (Host.mk z G) ∧
      n+tapeCharge cleanupWeight xs G ≤ tapeCharge cleanupWeight xs {S with R := park S.R}+price ∧ z.user = v.user ∧
      G.R archive = park S.R archive ∧ result G) →
    ∃ z G n, ∃ childOut : Stacks T prime, Exec body ((synStash archive separator xs).seq (call.seq ((Cover.Fallback.clearWorkTapes xs).seq (synUnstash archive separator xs))))
      (Host.mk u S) n (Host.mk z G) ∧ n ≤ price+4*owners.length+2*(owners.length*(2*V+3)+2)+1 ∧ z.user = u.user ∧ result childOut ∧
      (∀ j, j ∉ xs → j ≠ archive → G.L j = childOut.L j ∧ G.R j = childOut.R j) ∧
      (∀ j ∈ xs, G.L j = [] ∧ G.R j = S.R j) ∧ G.R archive = S.R archive := by
  intro port xs park off child
  have nd := distinct.map port.injective
  have encoded (i : Fin 142081) : S.R (port i) = List.ofFn (fun j => SparseRoleCircuit.encode (data i j)) := words.right i
  have width (j) (hj : j ∈ xs) : (S.R j).length = V := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    rw [encoded i,List.length_ofFn]
  obtain ⟨v,k,user,saveCost,save⟩ := stashRight_exec body archive separator xs nd off u S
  have empty (j) (hj : j ∈ xs) : S.L j = [] ∧ park S.R j = [] := by
    have ne : j ≠ archive := fun eq => off (eq ▸ hj)
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    exact ⟨words.left i,by simp [park,synClr,ne,hj]⟩
  obtain ⟨z,G,n,run,paid,same,regs,out⟩ := child v user empty
  let F := fun j => if j = archive ∨ j ∈ xs then S.R j else G.R j
  have keep (j) (hj : j ∈ xs) : F j = S.R j := ite_eq_left (Or.inr hj)
  have tail : F archive = S.R archive := ite_eq_left (Or.inl rfl)
  have safe (j) (hj : j ∈ xs) : separator ∉ F j := by
    rw [keep j hj]
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    rw [encoded i,List.mem_ofFn]
    rintro ⟨k,h⟩
    unfold SparseRoleCircuit.encode at h
    cases eq : decide (data i k = 1) <;> simp [eq,bitSymbol,separator,Fin.ext_iff] at h
  have entry : tapeCharge cleanupWeight xs {S with R := park S.R} = 4*owners.length := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun j hj => by
      simp [cleanupWeight,(empty j hj).1,(empty j hj).2])]
    simp [xs,Function.comp_def,List.map_const',Nat.mul_comm]
  rw [entry] at paid
  unfold tapeCharge cleanupWeight at paid
  obtain ⟨q,qu,clear⟩ := Cover.Fallback.clearWorkTapes_exec body xs nd z G
  have cleared : synClr G.R xs = park F := by
    funext j
    by_cases hj : j ∈ xs
    · have ne : j ≠ archive := fun eq => off (eq ▸ hj)
      simp [synClr,park,hj,ne]
    · by_cases h : j = archive
      · subst j
        simpa [synClr,hj,park] using regs
      · simp [synClr,park,F,hj,h]
  have ready : synClr G.R xs = Function.update (synClr F xs) archive
      (synStk F separator xs ++ separator :: S.R archive) := by
    simpa only [synStk_congr separator xs keep] using cleared
  obtain ⟨v',l,user',returnCost,reload⟩ := unstashRight_exec body archive separator xs nd off F
    (S.R archive) safe q {G with L := synClr G.L xs, R := synClr G.R xs} ready
  rw [← tail,Function.update_eq_self] at reload
  refine ⟨v',_,_,G,save.seq (run.seq (clear.seq reload)),?_,user'.trans (qu.trans (same.trans user)),out,?_,?_,tail⟩
  · rw [ownerStashCost S.R xs V width] at saveCost
    rw [ownerStashCost F xs V (fun j hj => keep j hj ▸ width j hj)] at returnCost
    have len : xs.length = owners.length := List.length_map _
    rw [len] at saveCost returnCost
    omega
  · intro j hj ne
    simp [synClr,F,hj,ne]
  · intro j hj
    exact ⟨ite_eq_left hj,keep j hj⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
