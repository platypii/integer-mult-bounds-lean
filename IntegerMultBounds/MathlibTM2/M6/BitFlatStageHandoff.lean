module

public import IntegerMultBounds.MathlibTM2.M6.BitPackedStageHandoff

/-! Return a flat stage's represented result as exact parent words for the next piece. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host SweepFile
open Shared50ModularControl (prime)

/-- Embed the worker on private tapes and copy its result once. The next
piece receives the same two controls and exact left-aligned owner words. -/
theorem flatWordStageHandoff {P U : Type} {T Q V : ℕ} (fan : Fin (142081+2) ↪ Fin T)
    (body : P → Pr P T Q prime U) (worker : Pr P T Q prime U) (seed : Stacks T prime)
    (effect : (Fin 142081 → Fin V → ZMod 2) → (Fin 142081 → Fin V → ZMod 2) → Prop)
    (price : ℝ)
    (run : ∀ x u S, ParentStageWords (fun i => fan (i.castAdd 2)) fan V x S →
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
  have live : ParentStageWords (fun i => fan (i.castAdd 2)) fan V x (embStk place S) :=
    ⟨words.left,words.right,words.controls⟩
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
  apply flatWordStageHandoff fan body worker seed effect price
  intro x u S words
  exact run x u S words.helperFan

/-- Run a seeded owner chart and return exact words to its successor. -/
theorem ownerChartHandoff {V Q : ℕ} {U : Type}
    (stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)))
    (seed : Stacks stage.tapes prime) (ready : ChartPrivateReady stage seed) (fits : stage.states ≤ Q) :
    ∃ (T : ℕ) (body : Empty → Pr Empty T Q prime U) (code : Pr Empty T Q prime U), ∃ src dst prepared,
      PackedPieceHandoff V (fun x y => y = stage.transform x) body code src dst prepared
        (stage.cost*(stage.tapes+5)+6+142081*(8*V+10)+1) := by
  let bank := Fin.castAddEmb 2 (n := stage.tapes)
  let fan := stageFan ⟨stage.slots,stage.slots_injective⟩
  let initial := adjacentStageStacks seed (⟨[],[],fun _ => [],fun _ => []⟩ : Stacks 2 prime)
  let body : Empty → Pr Empty (stage.tapes+2) Q prime U := Empty.elim
  have shared (i) : bank (stage.slots i) = fan (i.castAdd 2) := by
    simp [bank,fan,stageFan,@finSumFinEquiv_symm_apply_castAdd 142081 2]
  have apart (j : Fin 2) (i) : bank i ≠ fan (j.natAdd 142081) := by
    simp [bank,fan,stageFan,@finSumFinEquiv_symm_apply_natAdd 142081 2]
    intro eq
    have h := congrArg Fin.val eq
    change i.val = stage.tapes+j.val at h
    omega
  obtain ⟨code,prepared,handoff⟩ := flatStageHandoff fan body
    (embProg bank Empty.elim (foreign (liftQ stage.program fits))) initial
    (fun x y => y = stage.transform x) ((stage.cost*(stage.tapes+5)+6 : ℕ) : ℝ) (by
    intro x u S live stock
    have chart : ChartPrivateReady stage (embStk bank S) := by
      intro j outside z
      have away (t) : fan t ≠ bank j := by
        induction t using Fin.addCases with
        | left t => rw [← shared]; exact bank.injective.ne (outside t)
        | right t => exact (apart t j).symm
      obtain ⟨hl,hr⟩ := stock _ away
      simp only [embStk,Function.comp_apply,hl,hr]
      simpa [initial,bank,adjacentStageStacks] using ready j outside z
    obtain ⟨z,F,k,exec,paid,user,out,_⟩ := ownerStage_fan_exec stage bank fan shared apart fits body x u S chart live
    exact ⟨z,F,k,_,exec,by exact_mod_cast paid,user,out,rfl⟩)
  exact ⟨_,_,code,_,_,prepared,by simpa only [Nat.floor_natCast] using handoff⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
