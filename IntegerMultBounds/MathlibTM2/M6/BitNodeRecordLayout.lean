module

public import IntegerMultBounds.MathlibTM2.M6.BitNodeHeaderSetup

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Node M8.RevMachine
open Shared50ModularControl (prime)

private def clockSlots : Fin 7 ↪ Fin 34 := ⟨![3,8,9,10,11,12,13],by decide⟩
private def powerSlots : Fin 10 ↪ Fin 34 := ⟨![8,14,15,16,17,18,19,20,21,22],by decide⟩
private def divisionSlots : Fin 11 ↪ Fin 34 := Fin.natAddEmb 23
private instance (j : Fin 34) : Decidable (outsideArchiveOutputs clockSlots powerSlots j) :=
  inferInstanceAs (Decidable (_ ≠ _ ∧ _ ≠ _ ∧ _ ≠ _ ∧ _ ≠ _))

/-- The first six caller tapes hold the descriptor, followed by the cutoff and
payload lane. The remaining 26 tapes suffice for all header arithmetic. -/
theorem LoadsNodeSeedFromRecord.onLayout {Config : Type} {N : ℕ} {input : Config → CutoffNodeInput}
    {seed : Config → Stacks N prime} (loader : LoadsNodeSeedFromRecord input seed) :
    ∃ rate : ℕ, ∀ {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
      (bank : Fin N ↪ Fin T) (record : Fin 34 ↪ Fin T), (∀ i j, bank i ≠ record j) →
      ∃ code, ∀ x u (S : Stacks T prime), let c := input x
        (∀ i : Fin 6, S.R (record (i.castAdd 28)) = (Routines.hdr c.node i).map bitSymbol) →
        S.R (record 6) = binSyms c.root.width.size c.cutoff → (S.R (record 7)).length = c.cells →
        (∀ i : Fin 34, 8 ≤ i.val → S.R (record i) = []) →
        (∀ i, S.L (bank i) = [] ∧ S.R (bank i) = []) →
        ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F t (rate*c.cells) ∧
          (∀ i, F.L (bank i) = (seed x).L i ∧ F.R (bank i) = (seed x).R i) ∧
          ∀ j, (∀ i, bank i ≠ j) → (∀ i : Fin 34, 8 ≤ i.val → record i ≠ j) →
            F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨rate,load⟩ := loader
  refine ⟨rate,?_⟩
  intro P U T Q body bank record apart
  let fields := fun i : Fin 6 => record (i.castAdd 28)
  let clock := clockSlots.trans record
  let power := powerSlots.trans record
  let div := divisionSlots.trans record
  have frame (j : Fin 34) (h : outsideArchiveOutputs clockSlots powerSlots j) :
      outsideArchiveOutputs clock power (record j) :=
    ⟨record.injective.ne h.1,record.injective.ne h.2.1,record.injective.ne h.2.2.1,record.injective.ne h.2.2.2⟩
  obtain ⟨code,run⟩ := load body bank fields clock power (record 6) (record 7) div rfl rfl
    (fun i => record.injective.ne ((by decide : ∀ i, clockSlots 2 ≠ powerSlots i) i))
    (fun i => frame _ ((by decide : ∀ i : Fin 6, outsideArchiveOutputs clockSlots powerSlots (i.castAdd 28)) i))
    (frame _ (by decide)) (frame _ (by decide))
    (fun i => frame _ ((by decide : ∀ i, outsideArchiveOutputs clockSlots powerSlots (divisionSlots i)) i))
    (fun i => record.injective.ne ((by decide : ∀ i, (7 : Fin 34) ≠ divisionSlots i) i))
    (record.injective.ne (by decide : (6 : Fin 34) ≠ divisionSlots 2))
    (fun i => record.injective.ne ((by decide : ∀ i : Fin 6, i.castAdd 28 ≠ divisionSlots 2) i))
    (fun i j => by fin_cases j <;> exact apart i _) (fun i => apart i 7)
  refine ⟨code,?_⟩
  intro x u S c digits cut length scratch empty
  obtain ⟨z,F,t,exec,user,paid,ready,_,off⟩ := run x u S digits cut length
    (fun i h => scratch _ ((by decide : ∀ i : Fin 7, i ≠ 0 → 8 ≤ (clockSlots i).val) i h))
    (fun i h => scratch _ ((by decide : ∀ i : Fin 10, i ≠ 0 → 8 ≤ (powerSlots i).val) i h))
    (fun i => scratch _ ((by decide : ∀ i, 8 ≤ (divisionSlots i).val) i)) empty
  refine ⟨z,F,t,exec,user,paid,ready,?_⟩
  intro j bankOff scratchOff
  exact off j bankOff
    ⟨(scratchOff 8 (by decide)).symm,(scratchOff 9 (by decide)).symm,
     (scratchOff 14 (by decide)).symm,(scratchOff 16 (by decide)).symm⟩
    (scratchOff 25 (by decide)).symm

end IntegerMultBounds.MathlibTM2.M6.BitNode
