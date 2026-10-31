module

public import IntegerMultBounds.Machine.BinaryAdjacentWidthSelector
public import IntegerMultBounds.Machine.HeadTravel

/-! All-prefix machine head bounds for the concrete three-way width selector.
The allowance is linear in binary header lengths, independent of payload size. -/
@[expose] public section
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthSelector
variable {t a : ℕ}

theorem cost_length (hs ds : List Bool) : cost hs ds ≤ 4*(hs.length+ds.length)+27 := by
  have h := Less.cost_length hs ds
  have h' := Less.cost_length ds hs
  unfold cost
  omega

theorem prefix_heads (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (v : Tapes t a) (hs ds : List Bool)
    (hht : v.tape left = BinaryDescriptorStack.descriptor hs) (hhh : v.head left = 1)
    (hdt : v.tape right = BinaryDescriptorStack.descriptor ds) (hdh : v.head right = 1)
    (hft : v.tape flag = fun _ => blank) (hfh : v.head flag = 0)
    {n : ℕ} {c : Config t (Fintype.card (FiniteFlow.Control states)) a}
    (hrun : run (program left right flag hlr hlf hrf) n
      (v.start (program left right flag hlr hlf hrf)) = some c) (i : Fin t) :
    v.head i-(4*(hs.length+ds.length)+27) ≤ c.head i ∧
      c.head i ≤ v.head i+(4*(hs.length+ds.length)+27) := by
  obtain ⟨m,hm,z,hz,hh,_,_⟩ := selects left right flag hlr hlf hrf v hs ds hht hhh hdt hdh hft hfh
  have hn := (run_length_le_of_halt hrun hz hh).trans (hm.trans (cost_length hs ds))
  have ht := run_head_travel hrun i
  change v.head i-(n : ℤ) ≤ c.head i ∧ c.head i ≤ v.head i+(n : ℤ) at ht
  omega

end IntegerMultBounds.Machine.BinaryAdjacentWidthSelector
