module

public import IntegerMultBounds.MathlibTM2.M6.BitCutoffNode

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Certificates.PR589 IntervalDescriptor RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- Initialize all copies of the six dispatch headers from a single master bank. -/
theorem remainderWindowLoader {H N : ℕ} (origin : Fin H → Option (Fin (72+N)))
    (tmp saved : Fin H) (distinct : tmp ≠ saved) (freeTmp : origin tmp = none)
    (freeSaved : origin saved = none) :
    let words := fun (c : CutoffNodeInput) i =>
      idleDispatchWord c.w c.idleWidth c.root.width.size c.cutoff (idleSeedPorts i).val
    LoadsPackedSeed words CutoffNodeInput.cells (fun c =>
      remainderDispatchSeed origin c.w c.idleWidth c.root.width.size c.cutoff) := by
  classical
  intro words
  let active j := ∃ i, (origin j).map Fin.val = some (idleSeedPorts i).val
  let number := Fintype.equivFin {j // active j}
  let slots := number.symm.toEmbedding.trans (Function.Embedding.subtype active)
  have live i : active (slots i) := (number.symm i).property
  let field i := (live i).choose
  have hit i : (origin (slots i)).map Fin.val = some (idleSeedPorts (field i)).val := (live i).choose_spec
  have free j (blank : origin j = none) i : slots i ≠ j := by
    intro eq
    simpa [eq,blank] using hit i
  have load := LoadsPackedSeed.headers words CutoffNodeInput.cells slots field tmp saved
    distinct (free _ freeTmp) (free _ freeSaved) (49+93*H) (fun c => by
      apply (seedLoadBill_le slots _ (price := 8*((prime^(c.w+1)).size+c.idleWidth.size+2*c.w+c.root.width.size)+53) ?_).trans
      · have bound := c.remainderSetup_le H
        omega
      · intro i
        have h := Finset.single_le_sum (f := fun j => 8*(words c j).length+6)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (field i))
        have bill := idleDispatchSeed_cost c.w c.idleWidth c.root.width.size c.cutoff
        change (∑ j, (8*(words c j).length+6))+1 = _ at bill
        omega)
  convert load using 2
  rename_i c
  apply congrArg (fun r => Stacks.mk [] [] (fun _ => []) r)
  funext j
  by_cases present : active j
  · let i := number ⟨j,present⟩
    have eq : slots i = j := congrArg Subtype.val (number.symm_apply_apply ⟨j,present⟩)
    rw [← eq,slots.injective.extend_apply]
    change (origin (slots i)).elim [] _ = _
    cases h : origin (slots i) with
    | none => simpa [h] using hit i
    | some p =>
      have hv : p.val = (idleSeedPorts (field i)).val := by simpa [h] using hit i
      simp [hv,words]
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨i,rfl⟩; exact present (live i))]
    cases h : origin j with
    | none => rfl
    | some p =>
      apply idleDispatchWord_blank
      intro i eq
      exact present ⟨i,by simp [h,eq]⟩

/-- The assembled window reads each worker's headers from the same six master words. -/
theorem idleWindowDispatchLoader {Job : Type} {H N : ℕ}
    (origin : Fin H → Option (Σ _ : Job, Fin (72+N)))
    (free : ∃ a b, a ≠ b ∧ origin a = none ∧ origin b = none) :
    let words := fun (c : CutoffNodeInput) i =>
      idleDispatchWord c.w c.idleWidth c.root.width.size c.cutoff (idleSeedPorts i).val
    LoadsPackedSeed words CutoffNodeInput.cells (fun c =>
      idleWindowSeed origin (fun _ => idleDispatchStacks N c.w c.idleWidth c.root.width.size c.cutoff)) := by
  obtain ⟨a,b,ne,ha,hb⟩ := free
  intro words
  have load := remainderWindowLoader (fun j => (origin j).map Sigma.snd) a b ne
    (by simp [ha]) (by simp [hb])
  convert load using 2
  rename_i c
  apply congrArg₂ (fun l r => Stacks.mk [] [] l r)
  · funext j
    change (origin j).elim [] _ = []
    cases origin j <;> rfl
  · funext j
    change (origin j).elim [] _ = ((origin j).map Sigma.snd).elim [] _
    cases origin j <;> rfl

end IntegerMultBounds.MathlibTM2.M6.BitNode
