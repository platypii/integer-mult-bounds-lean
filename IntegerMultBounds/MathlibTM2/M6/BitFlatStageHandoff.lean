module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedStageHandoff

/-! Return a flat stage's represented result as exact parent words for the next piece. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host SweepFile
open Shared50ModularControl (prime)

/-- Embed the worker on private tapes and copy its result once. The next
piece receives the same two controls and exact left-aligned owner words. -/
theorem flatStageHandoff {P U : Type} {T Q V : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U) (seed : Stacks T prime)
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (price : ℝ)
    (run : ∀ x u S, HelperFan fan x S →
      (∀ j, (∀ i, fan i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F k y, Exec body worker (mk u S) k (mk z F) ∧ (k : ℝ) ≤ price ∧
        z.user = u.user ∧ HelperFan fan y F ∧ effect x y) :
    let place := Exit.chart 0 T
    let host := fun f => embProg place id (body f)
    ∃ code prepared, PackedPieceHandoff V effect host code (fan.trans place) (returnedFan fan)
      prepared (⌊price⌋₊+142081*(8*V+10)+1) := by
  classical
  intro place host
  let prepared : Stacks (Exit.size 0 T) prime :=
    ⟨seed.inp,seed.out,Function.extend place seed.L (fun _ => []),Function.extend place seed.R (fun _ => [])⟩
  obtain ⟨copy,materialize⟩ := packedResultWords_exec fan host
  refine ⟨(embProg place id worker).seq copy,prepared,?_⟩
  intro x u S words fresh
  have live : HelperFan fan x (embStk place S) := by
    have h := words.helperFan
    exact h
  obtain ⟨v,D,m,y,exec,time,user,out,act⟩ := run x (embDn place u) (embStk place S) live (by
    intro j outside
    have h := fresh (place j) (fun i => place.injective.ne (outside i))
    simpa [embStk,prepared,Function.comp_apply,place.injective.extend_apply] using h)
  obtain ⟨v',F,ran,_,same,view,off⟩ := exec_emb (ι := id) (body' := host) place.injective
    (fun _ => rfl) exec u rfl S rfl
  have blank j (away : ∀ i, place i ≠ j) : F.L j = [] ∧ F.R j = [] := by
    have unplaced : ¬ ∃ i, place i = j := by simpa using away
    have h := fresh j (fun i => away (fan i))
    obtain ⟨left,right⟩ := off j away
    simpa [prepared,Function.extend,unplaced] using And.intro (left.trans h.1) (right.trans h.2)
  let e := Fintype.equivFin (Exit.Register 0 T)
  have tmp := blank (Exit.tmp 0 T) (fun i => e.injective.ne (by intro h; cases h))
  rw [← view] at out
  obtain ⟨z,G,l,copied,paid,hz,result⟩ := materialize y v' F out tmp.1 tmp.2 (by
    intro i
    rw [returnedFan_owner]
    exact blank _ (fun i => e.injective.ne (by intro h; cases h)))
  exact ⟨z,G,m+l,y,Exec.seq ran copied,by have := Nat.le_floor time; omega,
    hz.trans (same.trans user),result,act⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
