module

public import IntegerMultBounds.MathlibTM2.M6.BitInheritedIdleRead

/-! Allocate disjoint private registers for a window of single-owner programs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host
open Shared50ModularControl (prime)

/-- A window host made from the caller tapes and one block per copy. The
initial stacks are the caller's on shared owners and the worker seed elsewhere. -/
theorem idleWorkspace {ι : Type} [Fintype ι] {B A : ℕ} (T : ι → ℕ)
    (owner : ι ↪ Fin B) (slot : ∀ i, Fin (T i)) :
    ∃ (H : ℕ) (caller : Fin B ↪ Fin H) (place : ∀ i, Fin (T i) ↪ Fin H),
      (∀ i, place i (slot i) = caller (owner i)) ∧
      (∀ i t, t ≠ owner i → ∀ k, place i k ≠ caller t) ∧
      (∀ i j, i ≠ j → ∀ k l, place i k ≠ place j l) ∧
      ∀ (S : Stacks B A) (seed : ∀ i, Stacks (T i) A),
      ∃ F : Stacks H A, embStk caller F = S ∧
        ∀ i k, k ≠ slot i → F.L (place i k) = (seed i).L k ∧ F.R (place i k) = (seed i).R k := by
  classical
  let Bank := Fin B ⊕ (Σ i, Fin (T i))
  let number := Fintype.equivFin Bank
  let base : Fin B ↪ Bank := ⟨Sum.inl,Sum.inl_injective⟩
  let route (i : ι) (k : Fin (T i)) : Bank :=
    if k = slot i then Sum.inl (owner i) else Sum.inr ⟨i,k⟩
  have inj i : Function.Injective (route i) := by
    intro k l eq
    by_cases hk : k = slot i <;> by_cases hl : l = slot i <;> simp_all [route] <;> cases eq <;> rfl
  let place (i : ι) := (⟨route i,inj i⟩ : Fin (T i) ↪ Bank).trans number.toEmbedding
  refine ⟨_,base.trans number.toEmbedding,place,?_,?_,?_,?_⟩
  · intro i
    simp [place,route,base]
  · intro i t ne k eq
    have hit := number.injective eq
    by_cases hk : k = slot i <;> simp_all [route,base] <;> cases hit <;> contradiction
  · intro i j ne k l eq
    have hit := number.injective eq
    by_cases hk : k = slot i <;> by_cases hl : l = slot j <;>
      simp_all [route,owner.injective.eq_iff] <;> first | exact ne (owner.injective (Sum.inl.inj hit)) | exact ne (congrArg Sigma.fst (Sum.inr.inj hit))
  · intro S seed
    let assemble (f : Fin B → List (Fin (A+4))) (g : ∀ i, Fin (T i) → List (Fin (A+4))) :=
      fun j => Sum.elim f (fun p => g p.1 p.2) (number.symm j)
    refine ⟨⟨S.inp,S.out,assemble S.L (fun i => (seed i).L),assemble S.R (fun i => (seed i).R)⟩,?_,?_⟩
    · cases S
      simp [embStk,assemble,base,Function.comp_def]
    · intro i k ne
      simp [place,route,ne,assemble]

/-- Allocate the copy programs and their procedure labels together. Starting
from exact owner words, each program receives its own seed outside its target. -/
theorem allocatedIdleWindow_exec {Q V : ℕ} {U : Type} (i : Fin 9) :
    let Job := (Fin 32 × Fin 5) × Fin 222
    ∀ (T : Job → ℕ) (P : Job → Type) (slot : ∀ k, Fin (T k))
      (inner : ∀ k, P k → Pr (P k) (T k) Q prime U) (code : ∀ k, Pr (P k) (T k) Q prime U)
      (seed : ∀ k, Stacks (T k) prime) (price : Job → ℕ)
      (effect : Job → (Fin V → ZMod 2) → (Fin V → ZMod 2) → Prop),
    (∀ k word v (D : Stacks (T k) prime), D.L (slot k) = [] →
      D.R (slot k) = List.ofFn (fun j => SparseRoleCircuit.encode (word j)) →
      (∀ j, j ≠ slot k → D.L j = (seed k).L j ∧ D.R j = (seed k).R j) →
      ∃ z F n y, Exec (inner k) (code k) (mk v D) n (mk z F) ∧ n ≤ price k ∧
        z.user = v.user ∧ Cover.Fallback.RecordPayload (slot k) (fun _ => blank) 0 y F ∧ effect k word y) →
    ∃ (H : ℕ) (fan : Fin (142081+2) ↪ Fin H) (host : (Σ k, P k) → Pr (Σ k, P k) H Q prime U)
      (program : Pr (Σ k, P k) H Q prime U),
    ∀ (x : Fin 142081 → Fin V → ZMod 2) (S : Stacks (142081+2) prime)
      (u : HS H Q prime U), HelperFan (Function.Embedding.refl _) x S →
      (∀ k, let t := (idleTape i k).castAdd 2
        S.L t = [] ∧ S.R t = List.ofFn (fun j => SparseRoleCircuit.encode (x (idleTape i k) j))) →
      ∃ D F z n y, embStk fan D = S ∧ Exec host program (mk u D) n (mk z F) ∧
        n ≤ (idleCopies.map price).sum+1 ∧ z.user = u.user ∧ HelperFan fan y F ∧
        (∀ k, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
        ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j := by
  intro Job T P slot inner code seed price effect run
  let owner : Job ↪ Fin (142081+2) :=
    (⟨idleTape i,idleTape_injective i⟩ : Job ↪ Fin 142081).trans (Fin.castAddEmb 2)
  obtain ⟨H,fan,place,shared,outside,apart,prepare⟩ := idleWorkspace (A := prime) T owner slot
  let host : (Σ k, P k) → Pr (Σ k, P k) H Q prime U :=
    fun p => embProg (place p.1) (Sigma.mk p.1) (inner p.1 p.2)
  refine ⟨H,fan,host,Prog.seqList (idleCopies.map fun k => embProg (place k) (Sigma.mk k) (code k)),?_⟩
  intro x S u live words
  obtain ⟨D,view,privateTapes⟩ := prepare S seed
  have ready : HelperFan fan x D := by
    change HelperFan (Function.Embedding.refl _) x (embStk fan D)
    rwa [view]
  obtain ⟨y,F,z,n,exec,paid,user,final,acts,off⟩ := placedIdleWindow_exec i host fan x D u ready
    T P place slot inner Sigma.mk code price effect shared outside apart (fun _ _ => rfl) (by
      intro k v E keep
      obtain ⟨left,right⟩ := keep (slot k)
      rw [shared] at left right
      have hl := congrArg (fun A => A.L (owner k)) view
      have hr := congrArg (fun A => A.R (owner k)) view
      exact run k _ v E (left.trans (hl.trans (words k).1)) (right.trans (hr.trans (words k).2))
        (fun j ne => ⟨(keep j).1.trans (privateTapes k j ne).1,(keep j).2.trans (privateTapes k j ne).2⟩))
  exact ⟨D,F,z,n,y,view,exec,paid,user,final,acts,off⟩

private theorem castWord {m n : ℕ} (h : m = n) (x : Fin n → Fin (prime+4)) :
    List.ofFn (fun k => x (k.cast h)) = List.ofFn x := by
  subst n
  rfl

private theorem inheritedWorkspaceSeed {B T N : ℕ} [NeZero T] (seed : Stacks N prime) :
    let slot := ((0 : Fin T).natAdd B).castAdd N
    ∃ initial : Stacks (B+T+N) prime, ∀ (D : Stacks (B+T+N) prime),
      D.L slot = [] → (∀ k, k ≠ slot → D.L k = initial.L k ∧ D.R k = initial.R k) →
      (∀ k : Fin T, D.L ((k.natAdd B).castAdd N) = []) ∧
      (∀ k : Fin T, k ≠ 0 → D.R ((k.natAdd B).castAdd N) = []) ∧
      (∀ k : Fin B, let t := (k.castAdd T).castAdd N; D.L t = [] ∧ D.R t = []) ∧
      (∀ k : Fin N, let t := k.natAdd (B+T); D.L t = seed.L k ∧ D.R t = seed.R k) := by
  intro slot
  let empty : Stacks (B+T) prime := ⟨seed.inp,seed.out,fun _ => [],fun _ => []⟩
  refine ⟨adjacentStageStacks empty seed,?_⟩
  intro D left keep
  have caller (k : Fin T) (h : k ≠ 0) := keep ((k.natAdd B).castAdd N)
    (((Fin.natAddEmb B).trans (Fin.castAddEmb N)).injective.ne h)
  refine ⟨fun k => ?_,fun k h => ?_,fun k => ?_,fun k => ?_⟩
  · by_cases h : k = 0
    · subst k
      exact left
    · simpa [adjacentStageStacks,empty] using (caller k h).1
  · simpa [adjacentStageStacks,empty] using (caller k h).2
  · apply (by simpa [adjacentStageStacks,empty] using keep ((k.castAdd T).castAdd N) : _)
    intro e
    have eq := congrArg Fin.val e
    change k.val = B + 0 at eq
    omega
  · apply (by simpa [adjacentStageStacks] using keep (k.natAdd (B+T)) : _)
    intro e
    have eq := congrArg Fin.val e
    change B + T + k.val = B + 0 at eq
    have pos := NeZero.pos T
    omega

/-- An inherited interval execution needs only its encoded target and a fixed
private seed. This is the worker contract of the allocated window. -/
theorem inheritedSeededWorker_exec {P U : Type} {N Q price : ℕ} {seed : Stacks N prime}
    (lane : RecursiveInterchangeLayout.Descriptor) {reads}
    (run : IntervalRun (P := P) (U := U) (Q := Q) seed price lane reads) :
    let T := intervalSplitTapes
    let H := 142082+T+N
    let slot := ((0 : Fin T).natAdd 142082).castAdd N
    let V := RecursiveInterchangeLayout.volume prime lane
    let wide := {lane with afterD := lane.afterD*142080}
    let m := RecursiveInterchangeLayout.volume prime wide
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U) (code : Pr (Empty ⊕ P) H Q prime U)
      (initial : Stacks H prime), ∀ (x : Fin m → ZMod 2) u (D : Stacks H prime),
      D.L slot = [] → D.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → D.L k = initial.L k ∧ D.R k = initial.R k) →
      ∃ z F n y, Exec host code (mk u D) n (mk z F) ∧
        n ≤ (149*(T+5)+5)*(V*142080)+24+((142081*(8*V+10)+1+price)+(149*(V*142080)*(T+5)+6)) ∧
        z.user = u.user ∧ Cover.Fallback.RecordPayload slot (fun _ => blank) 0 y F ∧ reads x y := by
  intro T H slot V wide m
  obtain ⟨host,code,exec⟩ := run
  obtain ⟨initial,prepare⟩ := inheritedWorkspaceSeed (B := 142082) (T := T) seed
  refine ⟨host,code,initial,?_⟩
  intro x u D left right privateTapes
  obtain ⟨hl,hr,fresh,child⟩ := prepare D left privateTapes
  obtain ⟨z,F,n,y,ran,paid,user,read,payload⟩ := exec x u D
    (right.trans (castWord _ _).symm) hl hr fresh child
  exact ⟨z,F,n,y,ran,paid,user,payload,read⟩

open RecursiveInterchangeLayout

private theorem transportWorker {a b H Q price : ℕ} {P U : Type} (size : a = b)
    (slot : Fin H) (host : P → Pr P H Q prime U) (code : Pr P H Q prime U)
    (initial : Stacks H prime) (effect : (Fin b → ZMod 2) → (Fin b → ZMod 2) → Prop) :
    let worker := fun (m : ℕ) (reads : (Fin m → ZMod 2) → (Fin m → ZMod 2) → Prop) =>
      ∀ (x : Fin m → ZMod 2) u (D : Stacks H prime), D.L slot = [] →
      D.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → D.L k = initial.L k ∧ D.R k = initial.R k) →
      ∃ z F n y, Exec host code (mk u D) n (mk z F) ∧ n ≤ price ∧ z.user = u.user ∧
        Cover.Fallback.RecordPayload slot (fun _ => blank) 0 y F ∧ reads x y
    worker a (fun x y => effect (fun k => x (k.cast size.symm)) (fun k => y (k.cast size.symm))) →
      worker b effect := by
  subst b
  exact id

/-- All selected idle owners execute their inherited interval child, with the
split and merge charged once per occurrence. -/
theorem inheritedWindow_exec {U : Type} {Q : ℕ} (i : Fin 9) (w W : ℕ) (positive : 0 < W)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let Job := (Fin 32 × Fin 5) × Fin 222
    let T := intervalSplitTapes
    let V := (prime^w)^128*W
    let m := (prime^w)^128*(W*142080)
    let lane := fun (k : Job) => let e := idleInterval i k.2; phaseIntervalChild e.1 e.2 w W 64
    ∀ (N : Job → ℕ) (P : Job → Type) (price : Job → ℕ)
      (body : ∀ k, P k → Pr (P k) (N k) Q prime U) (code : ∀ k, Pr (P k) (N k) Q prime U)
      (src dst : ∀ k, Fin (142081+2) ↪ Fin (N k)) (seed : ∀ k, Stacks (N k) prime),
    (∀ k, PackedPieceHandoff (volume prime (lane k)) (fun x y =>
      ∀ r : Fin 142080, y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd (lane k).rows) (x r.castSucc))
      (body k) (code k) (src k) (dst k) (seed k) (price k)) →
    ∃ (H : ℕ) (fan : Fin (142081+2) ↪ Fin H)
      (host : (Σ k, Empty ⊕ P k) → Pr (Σ k, Empty ⊕ P k) H Q prime U)
      (program : Pr (Σ k, Empty ⊕ P k) H Q prime U),
    ∀ (x : Fin 142081 → Fin m → ZMod 2) (S : Stacks (142081+2) prime)
      (u : HS H Q prime U), HelperFan (Function.Embedding.refl _) x S →
      (∀ k, let t := (idleTape i k).castAdd 2
        S.L t = [] ∧ S.R t = List.ofFn (fun j => SparseRoleCircuit.encode (x (idleTape i k) j))) →
      ∃ D F z n y, embStk fan D = S ∧ Exec host program (mk u D) n (mk z F) ∧
        n ≤ (idleCopies.map fun k => (149*(T+5)+5)*(V*142080)+24+
          ((142081*(8*V+10)+1+price k)+(149*(V*142080)*(T+5)+6))).sum+1 ∧
        z.user = u.user ∧ HelperFan fan y F ∧
        (∀ k, intervalChildRead i k.2 w (W*142080) (x (idleTape i k)) (y (idleTape i k))) ∧
        ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j := by
  intro Job T V m lane N P price body code src dst seed child
  have worker k := inheritedSeededWorker_exec (lane k)
    (inheritedIdleCopy_exec i k.2 w W positive capacity (child k))
  choose host program initial run using worker
  apply allocatedIdleWindow_exec i _ _ _ host program initial
  intro k
  have size : volume prime (lane k) = V :=
    intervalChild_volume (idleBounds i k.2).1 ((idleBounds i k.2).2.trans (by decide : 63 ≤ 64)) w W
  have physical : volume prime {lane k with afterD := (lane k).afterD*142080} = m := by
    change _ = (prime^w)^128*(W*142080)
    rw [← Nat.mul_assoc]
    change _ = V*142080
    rw [← size]
    simp [volume,Nat.mul_assoc]
  apply transportWorker physical _ _ _ _ (intervalChildRead i k.2 w (W*142080))
  simpa only [size] using run k

end IntegerMultBounds.MathlibTM2.M6.BitNode
