module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyLabel

/-! Pointwise additions between two banks of the PR589 node. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode

open IntegerMultBounds.Networks IntegerMultBounds.Machine
open Shared50ModularControl (prime)

abbrev BankLane := Fin 32 × Fin 111 × Fin 5

noncomputable def bankTape (b : Fin 8) (x : BankLane) : Fin 142081 :=
  ((Fin.cast card_role) (Fintype.equivFin Role ⟨x.1,b,x.2.1,x.2.2⟩)).castSucc

private theorem bankTape_eq {b c : Fin 8} {x y : BankLane} :
    bankTape b x = bankTape c y ↔ b = c ∧ x = y := by
  constructor
  · intro h
    have eq := (Fintype.equivFin Role).injective (Fin.cast_injective _ (Fin.castSucc_injective _ h))
    exact ⟨congrArg Role.bank eq,Prod.ext (congrArg Role.replica eq)
      (Prod.ext (congrArg Role.port eq) (congrArg Role.cls eq))⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Add the source bank to the destination in every replica, port and class.
The extra permanent tape and all other banks retain their words. -/
theorem bankAdd_stage (dst src : Fin 8) (distinct : dst ≠ src) {V : ℕ} (positive : 0 < V) :
    ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      stage.cost ≤ 76*17760*V ∧ ∀ data,
        (∀ x i, stage.transform data (bankTape dst x) i =
          data (bankTape dst x) i + data (bankTape src x) i) ∧
        ∀ j, (∀ x, bankTape dst x ≠ j) → stage.transform data j = data j := by
  classical
  let lanes := Fintype.equivFin BankLane
  let entries := List.ofFn fun i => (lanes.symm i,lanes.symm i)
  have lengthEntries : entries.length = 17760 := (List.length_ofFn).trans (by simp only [BankLane,Fintype.card_prod,Fintype.card_fin])
  have off (x y : BankLane) : bankTape dst x ≠ bankTape src y :=
    fun h => distinct (bankTape_eq.mp h).1
  obtain ⟨stage,bill,effect⟩ := ownerAdds_stage (bankTape dst) (bankTape src) off entries positive
  refine ⟨stage,?_,fun data => ⟨?_,?_⟩⟩
  · simpa only [lengthEntries] using bill
  · intro x i
    rw [effect,SparseCircuit.copies_run _ _ _ off]
    simp only [entries,List.map_ofFn,List.sum_ofFn,Function.comp_apply,bankTape_eq,true_and,Equiv.symm_apply_eq]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,Equiv.symm_apply_apply]
  · intro j untouched
    funext i
    rw [effect,SparseCircuit.copies_run _ _ _ off]
    simp only [entries,List.map_ofFn,List.sum_ofFn,Function.comp_apply,untouched,ite_false,Finset.sum_const_zero,add_zero]

/-- The two directed bank additions of a bridge, including their physical join. -/
theorem bridge_stage (d s : Fin 4) (distinct : d ≠ s) {V : ℕ} (positive : 0 < V) :
    let even := fun p : Fin 4 => (⟨2*p.val,by omega⟩ : Fin 8)
    let odd := fun p : Fin 4 => (⟨2*p.val+1,by omega⟩ : Fin 8)
    ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      stage.cost ≤ 2*(76*17760*V)+1 ∧ ∀ data,
        (∀ x i, stage.transform data (bankTape (even d) x) i =
          data (bankTape (even d) x) i + data (bankTape (even s) x) i) ∧
        (∀ x i, stage.transform data (bankTape (odd s) x) i =
          data (bankTape (odd s) x) i + data (bankTape (odd d) x) i) ∧
        ∀ j, (∀ x, bankTape (even d) x ≠ j) → (∀ x, bankTape (odd s) x ≠ j) →
          stage.transform data j = data j := by
  intro even odd
  have vals := Fin.val_ne_of_ne distinct
  have ed : even d ≠ even s := fun h => by have := congrArg Fin.val h; dsimp [even] at this; omega
  have os : odd s ≠ odd d := fun h => by have := congrArg Fin.val h; dsimp [odd] at this; omega
  have parity (p q : Fin 4) (x y : BankLane) : bankTape (even p) x ≠ bankTape (odd q) y := by
    intro h
    have := congrArg Fin.val (bankTape_eq.mp h).1
    dsimp [even,odd] at this
    omega
  obtain ⟨a,ca,ha⟩ := bankAdd_stage _ _ ed positive
  obtain ⟨b,cb,hb⟩ := bankAdd_stage _ _ os positive
  refine ⟨SharedBankStage.compose a b,?_,fun data => ?_⟩
  · change a.cost+b.cost+1 ≤ _
    omega
  · obtain ⟨ae,af⟩ := ha data
    obtain ⟨be,bf⟩ := hb (a.transform data)
    change (∀ x i, b.transform (a.transform data) _ i = _) ∧ _
    refine ⟨fun x i => ?_,fun x i => ?_,fun j e o => (bf j o).trans (af j e)⟩
    · rw [bf _ (fun y => (parity _ _ x y).symm),ae]
    · change b.transform (a.transform data) _ i = _
      rw [be,af _ (fun y => parity _ _ y x),af _ (fun y => parity _ _ y x)]

/-- Three XOR additions exchange two complete banks. -/
theorem bankSwap_stage (d s : Fin 8) (distinct : d ≠ s) {V : ℕ} (positive : 0 < V) :
    ∃ stage : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := V)),
      stage.cost ≤ 3*(76*17760*V)+2 ∧ ∀ data,
        (∀ x, stage.transform data (bankTape d x) = data (bankTape s x)) ∧
        (∀ x, stage.transform data (bankTape s x) = data (bankTape d x)) ∧
        ∀ j, (∀ x, bankTape d x ≠ j) → (∀ x, bankTape s x ≠ j) →
          stage.transform data j = data j := by
  have off (x y : BankLane) : bankTape d x ≠ bankTape s y :=
    fun h => distinct (bankTape_eq.mp h).1
  obtain ⟨a,ca,ha⟩ := bankAdd_stage _ _ distinct positive
  obtain ⟨b,cb,hb⟩ := bankAdd_stage _ _ distinct.symm positive
  refine ⟨SharedBankStage.compose (SharedBankStage.compose a b) a,?_,fun data => ?_⟩
  · change a.cost+b.cost+1+a.cost+1 ≤ _
    omega
  · obtain ⟨ae,af⟩ := ha data
    obtain ⟨be,bf⟩ := hb (a.transform data)
    obtain ⟨ce,cf⟩ := ha (b.transform (a.transform data))
    have mid (x : BankLane) (i : Fin V) : b.transform (a.transform data) (bankTape s x) i =
        data (bankTape d x) i := by
      rw [be,af _ (fun y => off y x),ae]
      generalize data (bankTape d x) i = u
      generalize data (bankTape s x) i = v
      revert u v
      decide
    refine ⟨fun x => ?_,fun x => ?_,fun j hd hs => (cf j hd).trans ((bf j hs).trans (af j hd))⟩
    · funext i
      change a.transform (b.transform (a.transform data)) _ i = _
      rw [ce,mid,bf _ (fun y => (off x y).symm),ae]
      generalize data (bankTape d x) i = u
      generalize data (bankTape s x) i = v
      revert u v
      decide
    · funext i
      change a.transform (b.transform (a.transform data)) _ i = _
      rw [cf _ (fun y => off y x),mid]

end IntegerMultBounds.MathlibTM2.M6.BitNode
