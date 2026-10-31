module

public import IntegerMultBounds.Machine.BinaryAdjacentWidthSelectorDispatch
public import IntegerMultBounds.Machine.HoareWithinFiniteFlow

/-! The physical three-way width selector and its selected halting branch
share one prefix predicate, including the actual branch-entry transition. -/
@[expose] public section
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthSelectorDispatchWithin
noncomputable section
variable {t a e h d : ℕ}
open BinaryAdjacentWidthSelectorDispatch

theorem runs (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (equal : Program t e a) (longH : Program t h a) (longD : Program t d a)
    (v equalOut longHOut longDOut : Tapes t a) (equalCost longHCost longDCost : ℕ)
    (hs ds : List Bool)
    (hht : v.tape left = BinaryDescriptorStack.descriptor hs) (hhh : v.head left = 1)
    (hdt : v.tape right = BinaryDescriptorStack.descriptor ds) (hdh : v.head right = 1)
    (hft : v.tape flag = fun _ => blank) (hfh : v.head flag = 0)
    (lo upper : ℤ)
    (hm : ∀ j, lo+(BinaryAdjacentWidthSelector.cost hs ds : ℕ) ≤ v.head j ∧
      v.head j+(BinaryAdjacentWidthSelector.cost hs ds : ℕ) ≤ upper)
    (equalRuns : Counter.value hs = Counter.value ds →
      HoareWithin equal (fun w => w = v) (fun w => w = equalOut) equalCost (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper))
    (longHRuns : Counter.value ds < Counter.value hs →
      HoareWithin longH (fun w => w = v) (fun w => w = longHOut) longHCost (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper))
    (longDRuns : Counter.value hs < Counter.value ds →
      HoareWithin longD (fun w => w = v) (fun w => w = longDOut) longDCost (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper)) :
    HoareWithin (program left right flag hlr hlf hrf equal longH longD)
      (fun w => w = v)
      (fun w => w = chosen (Counter.value hs) (Counter.value ds) equalOut longHOut longDOut)
      (BinaryAdjacentWidthSelector.cost hs ds+1+
        chosen (Counter.value hs) (Counter.value ds) equalCost longHCost longDCost) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ upper) := by
  obtain ⟨n,hn,c,hr,hh,ht,hstate⟩ :=
    BinaryAdjacentWidthSelector.selects left right flag hlr hlf hrf v hs ds hht hhh hdt hdh hft hfh
  let fam := family left right flag hlr hlf hrf equal longH longD
  have hrs := RunWithin.heads_of_run_le hr hn lo upper hm
  change RunWithin (fam 0) _ n (v.start (fam 0)) c at hrs
  by_cases hd : Counter.value hs < Counter.value ds
  · have hedge : next (e := e) (h := h) (d := d) 0 c.state = some 3 := by
      rw [hstate,next_selected]
      simp only [chosen,ite_eq_left hd]
    have hc := FiniteFlow.jump_then_halt_within fam next 0 3 hrs hh hedge
      ((longDRuns hd).consequence (fun _ hw => hw.trans ht) (fun _ hw => hw) le_rfl (fun _ hw => hw))
      (by intro st; rfl)
    apply hc.consequence (fun _ hw => hw) _ _ (fun _ hw => hw)
    · intro w hw
      simpa only [chosen,ite_eq_left hd] using hw
    · simp only [chosen,ite_eq_left hd]
      omega
  · by_cases hl : Counter.value ds < Counter.value hs
    · have hedge : next (e := e) (h := h) (d := d) 0 c.state = some 2 := by
        rw [hstate,next_selected]
        simp only [chosen,ite_eq_right hd,ite_eq_left hl]
      have hc := FiniteFlow.jump_then_halt_within fam next 0 2 hrs hh hedge
        ((longHRuns hl).consequence (fun _ hw => hw.trans ht) (fun _ hw => hw) le_rfl (fun _ hw => hw))
        (by intro st; rfl)
      apply hc.consequence (fun _ hw => hw) _ _ (fun _ hw => hw)
      · intro w hw
        simpa only [chosen,ite_eq_right hd,ite_eq_left hl] using hw
      · simp only [chosen,ite_eq_right hd,ite_eq_left hl]
        omega
    · have he : Counter.value hs = Counter.value ds := by omega
      have hedge : next (e := e) (h := h) (d := d) 0 c.state = some 1 := by
        rw [hstate,next_selected]
        simp only [chosen,ite_eq_right hd,ite_eq_right hl]
      have hc := FiniteFlow.jump_then_halt_within fam next 0 1 hrs hh hedge
        ((equalRuns he).consequence (fun _ hw => hw.trans ht) (fun _ hw => hw) le_rfl (fun _ hw => hw))
        (by intro st; rfl)
      apply hc.consequence (fun _ hw => hw) _ _ (fun _ hw => hw)
      · intro w hw
        simpa only [chosen,ite_eq_right hd,ite_eq_right hl] using hw
      · simp only [chosen,ite_eq_right hd,ite_eq_right hl]
        omega

end
end IntegerMultBounds.Machine.BinaryAdjacentWidthSelectorDispatchWithin
