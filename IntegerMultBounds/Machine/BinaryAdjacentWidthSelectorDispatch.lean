import IntegerMultBounds.Machine.BinaryAdjacentWidthSelector

/-! Generic finite-flow composition of the actual three-way width selector
with three supplied branch programs. This composition rule does not assert
that the final concrete binary interchange wrapper has been instantiated. -/
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthSelectorDispatch
noncomputable section
variable {t a e h d : ℕ}

abbrev selectorStates := Fintype.card (FiniteFlow.Control BinaryAdjacentWidthSelector.states)
abbrev states (e h d : ℕ) : Fin 4 → ℕ := ![selectorStates,e,h,d]

def family (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (equal : Program t e a) (longH : Program t h a) (longD : Program t d a) :
    (pc : Fin 4) → Program t (states e h d pc) a :=
  Fin.cases (BinaryAdjacentWidthSelector.program left right flag hlr hlf hrf)
    (Fin.cases equal (Fin.cases longH (Fin.cases longD (fun i => Fin.elim0 i))))

def next : FiniteFlow.Next (states e h d) :=
  Fin.cases (fun (st : Fin selectorStates) =>
      if st = BinaryAdjacentWidthSelector.equalState then some 1 else
      if st = BinaryAdjacentWidthSelector.longHState then some 2 else some 3)
    (fun _ _ => none)

def program (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (equal : Program t e a) (longH : Program t h a) (longD : Program t d a) :=
  FiniteFlow.program (family left right flag hlr hlf hrf equal longH longD) next 0

def chosen {α : Type*} (uH uD : ℕ) (equal longH longD : α) :=
  if uH < uD then longD else if uD < uH then longH else equal

theorem next_selected (uH uD : ℕ) :
    next (e := e) (h := h) (d := d) 0 (BinaryAdjacentWidthSelector.selected uH uD) =
      some (chosen uH uD 1 2 3) := by
  change (if BinaryAdjacentWidthSelector.selected uH uD = BinaryAdjacentWidthSelector.equalState then some 1 else
    if BinaryAdjacentWidthSelector.selected uH uD = BinaryAdjacentWidthSelector.longHState then some 2 else some 3) = _
  simp only [BinaryAdjacentWidthSelector.selected_equal_iff,BinaryAdjacentWidthSelector.selected_longH_iff]
  unfold chosen
  by_cases hh : uH < uD
  · have he : uH ≠ uD := by omega
    have hl : ¬uD < uH := by omega
    simp only [ite_eq_left hh,ite_eq_right he,ite_eq_right hl]
  · by_cases hd : uD < uH
    · have he : uH ≠ uD := by omega
      simp only [ite_eq_right hh,ite_eq_right he,ite_eq_left hd]
    · have he : uH = uD := by omega
      simp only [ite_eq_right hh,ite_eq_left he,ite_eq_right hd]

/-- Selector cleanup precedes the actual finite-control jump. Every chosen
branch then halts the whole machine, with its conditional runtime charged. -/
theorem runs (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (equal : Program t e a) (longH : Program t h a) (longD : Program t d a)
    (v equalOut longHOut longDOut : Tapes t a) (equalCost longHCost longDCost : ℕ)
    (hs ds : List Bool)
    (hht : v.tape left = BinaryDescriptorStack.descriptor hs) (hhh : v.head left = 1)
    (hdt : v.tape right = BinaryDescriptorStack.descriptor ds) (hdh : v.head right = 1)
    (hft : v.tape flag = fun _ => blank) (hfh : v.head flag = 0)
    (equalRuns : Counter.value hs = Counter.value ds →
      HoareTime equal (fun w => w = v) (fun w => w = equalOut) equalCost)
    (longHRuns : Counter.value ds < Counter.value hs →
      HoareTime longH (fun w => w = v) (fun w => w = longHOut) longHCost)
    (longDRuns : Counter.value hs < Counter.value ds →
      HoareTime longD (fun w => w = v) (fun w => w = longDOut) longDCost) :
    HoareTime (program left right flag hlr hlf hrf equal longH longD)
      (fun w => w = v)
      (fun w => w = chosen (Counter.value hs) (Counter.value ds) equalOut longHOut longDOut)
      (BinaryAdjacentWidthSelector.cost hs ds+1+
        chosen (Counter.value hs) (Counter.value ds) equalCost longHCost longDCost) := by
  obtain ⟨n,hn,c,hr,hh,ht,hstate⟩ :=
    BinaryAdjacentWidthSelector.selects left right flag hlr hlf hrf v hs ds hht hhh hdt hdh hft hfh
  let fam := family left right flag hlr hlf hrf equal longH longD
  by_cases hd : Counter.value hs < Counter.value ds
  · obtain ⟨m,z,hm,hzr,hzh,hzout⟩ := longDRuns hd v rfl
    have htail : FiniteFlow.Trace fam next 3 c.tapes m 3 z := by
      rw [ht]
      exact .stop (family := fam) (next := next) 3 v m z hzr hzh rfl
    have hedge : next (e := e) (h := h) (d := d) 0 c.state = some 3 := by
      rw [hstate,next_selected]
      simp only [chosen,ite_eq_left hd]
    have htrace : FiniteFlow.Trace fam next 0 v (n+1+m) 3 z :=
      .join (family := fam) (next := next) 0 3 3 v n m c z hr hh hedge htail
    have hc := FiniteFlow.trace_hoare fam next htrace
    apply hc.consequence (fun _ hw => hw) _ _
    · intro w hw
      simpa only [chosen,ite_eq_left hd] using hw.trans hzout
    · simp only [chosen,ite_eq_left hd]
      omega
  · by_cases hl : Counter.value ds < Counter.value hs
    · obtain ⟨m,z,hm,hzr,hzh,hzout⟩ := longHRuns hl v rfl
      have htail : FiniteFlow.Trace fam next 2 c.tapes m 2 z := by
        rw [ht]
        exact .stop (family := fam) (next := next) 2 v m z hzr hzh rfl
      have hedge : next (e := e) (h := h) (d := d) 0 c.state = some 2 := by
        rw [hstate,next_selected]
        simp only [chosen,ite_eq_right hd,ite_eq_left hl]
      have htrace : FiniteFlow.Trace fam next 0 v (n+1+m) 2 z :=
        .join (family := fam) (next := next) 0 2 2 v n m c z hr hh hedge htail
      have hc := FiniteFlow.trace_hoare fam next htrace
      apply hc.consequence (fun _ hw => hw) _ _
      · intro w hw
        simpa only [chosen,ite_eq_right hd,ite_eq_left hl] using hw.trans hzout
      · simp only [chosen,ite_eq_right hd,ite_eq_left hl]
        omega
    · have he : Counter.value hs = Counter.value ds := by omega
      obtain ⟨m,z,hm,hzr,hzh,hzout⟩ := equalRuns he v rfl
      have htail : FiniteFlow.Trace fam next 1 c.tapes m 1 z := by
        rw [ht]
        exact .stop (family := fam) (next := next) 1 v m z hzr hzh rfl
      have hedge : next (e := e) (h := h) (d := d) 0 c.state = some 1 := by
        rw [hstate,next_selected]
        simp only [chosen,ite_eq_right hd,ite_eq_right hl]
      have htrace : FiniteFlow.Trace fam next 0 v (n+1+m) 1 z :=
        .join (family := fam) (next := next) 0 1 1 v n m c z hr hh hedge htail
      have hc := FiniteFlow.trace_hoare fam next htrace
      apply hc.consequence (fun _ hw => hw) _ _
      · intro w hw
        simpa only [chosen,ite_eq_right hd,ite_eq_right hl] using hw.trans hzout
      · simp only [chosen,ite_eq_right hd,ite_eq_right hl]
        omega

/-- Common-output specialization with canonical descriptor costs absorbed by
one positive volume. Supplied branch contracts remain explicit. -/
theorem runs_same_volume (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (equal : Program t e a) (longH : Program t h a) (longD : Program t d a)
    (v out : Tapes t a) (equalCost longHCost longDCost V : ℕ) (hV : 0 < V)
    (hs ds : List Bool) (hc : GrowingCounterData.Canonical hs) (dc : GrowingCounterData.Canonical ds)
    (hb : Counter.value hs ≤ V) (db : Counter.value ds ≤ V)
    (hht : v.tape left = BinaryDescriptorStack.descriptor hs) (hhh : v.head left = 1)
    (hdt : v.tape right = BinaryDescriptorStack.descriptor ds) (hdh : v.head right = 1)
    (hft : v.tape flag = fun _ => blank) (hfh : v.head flag = 0)
    (equalRuns : Counter.value hs = Counter.value ds →
      HoareTime equal (fun w => w = v) (fun w => w = out) equalCost)
    (longHRuns : Counter.value ds < Counter.value hs →
      HoareTime longH (fun w => w = v) (fun w => w = out) longHCost)
    (longDRuns : Counter.value hs < Counter.value ds →
      HoareTime longD (fun w => w = v) (fun w => w = out) longDCost) :
    HoareTime (program left right flag hlr hlf hrf equal longH longD)
      (fun w => w = v) (fun w => w = out)
      (43*V+1+chosen (Counter.value hs) (Counter.value ds) equalCost longHCost longDCost) := by
  have hh := runs left right flag hlr hlf hrf equal longH longD v out out out
    equalCost longHCost longDCost hs ds hht hhh hdt hdh hft hfh equalRuns longHRuns longDRuns
  have hb' := BinaryAdjacentWidthSelector.cost_volume hs ds hc dc V hV hb db
  apply hh.consequence (fun _ h => h) _ (by omega)
  intro w hw
  simpa only [chosen,ite_self] using hw

end
end IntegerMultBounds.Machine.BinaryAdjacentWidthSelectorDispatch
