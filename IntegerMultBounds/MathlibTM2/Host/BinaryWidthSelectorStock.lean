module

public import IntegerMultBounds.MathlibTM2.Host.ForeignStock
public import IntegerMultBounds.Machine.BinaryAdjacentWidthSelector

/-! The concrete interchange width selector uses linear header storage.
Its runtime is linear in header lengths, so the native simulator bound suffices;
this argument is deliberately confined to selection, not the interchange body. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Host.BinaryWidthSelectorStock
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
abbrev states := Fintype.card (FiniteFlow.Control BinaryAdjacentWidthSelector.states)
variable {T A : ℕ} {P U : Type}

theorem cost_length (hs ds : List Bool) :
    BinaryAdjacentWidthSelector.cost hs ds ≤ 4*(hs.length+ds.length)+27 := by
  have h := BinaryAdjacentWidthSelector.Less.cost_length hs ds
  have h' := BinaryAdjacentWidthSelector.Less.cost_length ds hs
  unfold BinaryAdjacentWidthSelector.cost
  omega

/-- Execute the actual placed three-way selector. The complete represented tape
bank restores, and every host configuration has linear header workspace. -/
theorem exec_within (body : P → Pr P T states A U)
    (left right flag : Fin T) (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (w : Tapes T A) (hs ds : List Bool)
    (hht : w.tape left = BinaryDescriptorStack.descriptor hs) (hhh : w.head left = 1)
    (hdt : w.tape right = BinaryDescriptorStack.descriptor ds) (hdh : w.head right = 1)
    (hft : w.tape flag = fun _ => blank) (hfh : w.head flag = 0)
    (v : HS T states A U) (S : Stacks T A) (hrep : RepT w S.L S.R) (depth : ℕ) :
    ∃ v' S', RepT w S'.L S'.R ∧ v'.user = v.user ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      ∃ n ≤ (4*(hs.length+ds.length)+27)*(T+5)+6,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*((4*(hs.length+ds.length)+27)*(T+5)+6)) depth
        (foreign (BinaryAdjacentWidthSelector.program left right flag hlr hlf hrf))
        (mk v S) n (mk v' S') := by
  have h := BinaryAdjacentWidthSelector.preserves left right flag hlr hlf hrf w hs ds hht hhh hdt hdh hft hfh
  obtain ⟨v',S',w',hw,hr,hu,hi,ho,n,hn,he⟩ := foreign_exec_within_time _ body h v S w rfl hrep depth
  subst w'
  have hb := Nat.add_le_add_right (Nat.mul_le_mul_right (T+5) (cost_length hs ds)) 6
  exact ⟨v',S',hr,hu,hi,ho,n,hn.trans hb,he.mono (by intro d z hz; omega)⟩

end IntegerMultBounds.MathlibTM2.Host.BinaryWidthSelectorStock
