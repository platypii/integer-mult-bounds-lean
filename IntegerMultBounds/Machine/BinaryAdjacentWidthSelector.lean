import IntegerMultBounds.Machine.ArbitraryWidthHighBranchPlacement
import IntegerMultBounds.Machine.BinaryCanonicalData
import IntegerMultBounds.Machine.FiniteFlow
import IntegerMultBounds.Machine.Placement

/-! Paid strict comparison of the two original binary widths, read from the retained canonical
binary descriptors. The comparison flag is physically erased in the selecting
transition, and all descriptor cells and heads are restored. -/
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthSelector.Less
noncomputable section
variable {a : ℕ}

/-- Local tapes are the two widths and one initially blank comparison flag. -/
abbrev input (rs es : List Bool) : Tapes 3 a := BinaryDescriptorCompare.input rs es

def high : Fin 3 := 1
def fallback : Fin 3 := 2

def selected (r e : ℕ) : Fin 3 := if r < e then high else fallback

def finish : Program 3 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st = 0 then
    some (if sy 2 = bitSymbol true then high else fallback,
      fun i => (if i = 2 then blank else sy i,Move.stay))
    else none

def cfg (v : Tapes 3 a) (st : Fin 3) : Config 3 3 a := ⟨st,v.head,v.tape⟩

theorem finish_test (rs es : List Bool) :
    (BinaryDescriptorCompare.output (q := a) rs es).reads 2 = bitSymbol true ↔
      Counter.value rs < Counter.value es := by
  change bitSymbol (a := a) (decide (Counter.value rs < Counter.value es)) = bitSymbol true ↔ _
  by_cases h : Counter.value rs < Counter.value es <;> simp [h,bitSymbol,Fin.ext_iff]

theorem finish_step (rs es : List Bool) :
    step (finish (a := a)) ((BinaryDescriptorCompare.output rs es).start finish) =
      some (cfg (input rs es) (selected (Counter.value rs) (Counter.value es))) := by
  have htest := finish_test (a := a) rs es
  simp only [Tapes.reads] at htest
  simp only [step,Tapes.start,finish,ite_true,htest]
  change some (Config.mk (selected (Counter.value rs) (Counter.value es)) _ _) =
    some (cfg (input rs es) (selected (Counter.value rs) (Counter.value es)))
  congr 1
  apply congrArg₂ (Config.mk (selected (Counter.value rs) (Counter.value es)))
  · funext i
    fin_cases i <;> rfl
  · funext i z
    fin_cases i <;> by_cases hz : z = 0
    all_goals simp [input,BinaryDescriptorCompare.input,BinaryDescriptorCompare.output,
      BinaryDescriptorCompare.bank,BinaryCompare.cfg,Config.tapes,BinaryDescriptorCompare.result,hz]
    all_goals intro he; rw [he]

theorem finish_halt (rs es : List Bool) :
    step (finish (a := a)) (cfg (input rs es) (selected (Counter.value rs) (Counter.value es))) = none := by
  unfold selected
  split_ifs <;> simp [step,finish,cfg,high,fallback]

abbrev states : Fin 2 → ℕ := ![12,3]
def family : (pc : Fin 2) → Program 3 (states pc) a :=
  Fin.cases BinaryDescriptorCompare.program (Fin.cases finish (fun i => Fin.elim0 i))
def next : FiniteFlow.Next states := Fin.cases (fun _ => some 1) (fun _ _ => none)
def program := FiniteFlow.program (family (a := a)) next 0

def result (rs es : List Bool) : Config 3 (Fintype.card (FiniteFlow.Control states)) a :=
  (cfg (input rs es) (selected (Counter.value rs) (Counter.value es))).mapState
    (FiniteFlow.embed states 1)

def cost (rs es : List Bool) := BinaryDescriptorCompare.cost rs es+2

/-- The literal terminal finite state records whether the first width is less
than the second. The flag and all scratch are blank at that boundary. -/
theorem selects (rs es : List Bool) :
    ∃ n ≤ cost rs es, run (program (a := a)) n ((input rs es).start program) = some (result rs es) ∧
      step (program (a := a)) (result rs es) = none := by
  obtain ⟨n,c,hn,hr,hh,hout⟩ := BinaryDescriptorCompare.compare_hoare (q := a) rs es _ rfl
  have hf := finish_step (a := a) rs es
  have hhalt := finish_halt (a := a) rs es
  have ht : FiniteFlow.Trace (family (a := a)) next 1 (BinaryDescriptorCompare.output rs es) 1 1
      (cfg (input rs es) (selected (Counter.value rs) (Counter.value es))) :=
    .stop 1 _ 1 _ (by
      change run (finish (a := a)) 1 ((BinaryDescriptorCompare.output rs es).start finish) = _
      exact hf) (by exact hhalt) rfl
  rw [← hout] at ht
  have ht' : FiniteFlow.Trace (family (a := a)) next 0 (input rs es) (n+1+1) 1
      (cfg (input rs es) (selected (Counter.value rs) (Counter.value es))) :=
    .join 0 1 1 _ n 1 c _ (by
      change run (BinaryDescriptorCompare.program (q := a)) n ((input rs es).start BinaryDescriptorCompare.program) = some c
      exact hr) (by exact hh) rfl ht
  have hrun := FiniteFlow.trace_run (family (a := a)) next 0 ht'
  exact ⟨n+1+1,by unfold cost; omega,hrun⟩

theorem preserves (rs es : List Bool) :
    HoareTime (program (a := a)) (fun v => v = input rs es) (fun v => v = input rs es) (cost rs es) := by
  obtain ⟨n,hn,hr,hh⟩ := selects (a := a) rs es
  rintro v rfl
  exact ⟨n,result rs es,hn,hr,hh,rfl⟩

theorem cost_length (rs es : List Bool) : cost rs es ≤ 2*(rs.length+es.length)+13 := by
  unfold cost BinaryDescriptorCompare.cost
  omega

theorem cost_value (rs es : List Bool)
    (cr : GrowingCounterData.Canonical rs) (ce : GrowingCounterData.Canonical es) :
    cost rs es ≤ 2*(Counter.value rs+Counter.value es)+17 := by
  have hr := (GrowingCounterData.canonical_width rs cr).trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have he := (GrowingCounterData.canonical_width es ce).trans (Nat.add_le_add_right (Nat.log2_le_self _) 1)
  have h := cost_length rs es
  omega

theorem cost_volume (rs es : List Bool)
    (cr : GrowingCounterData.Canonical rs) (ce : GrowingCounterData.Canonical es)
    (V : ℕ) (hV : 0 < V) (hr : Counter.value rs ≤ V) (he : Counter.value es ≤ V) :
    cost rs es ≤ 21*V := by
  have h := cost_value rs es cr ce
  omega

/-- The explicit true/false terminal state remains visible when the three
local tapes are placed into any larger machine bank; all other tapes are
preserved without active-view assumptions in the postcondition. -/
theorem selects_at {t u : ℕ} (placement : Fin (3+u) ≃ Fin t) (v : Tapes t a)
    (rs es : List Bool)
    (ha : Placement.active placement v = input rs es) :
    ∃ n ≤ cost rs es, ∃ c,
      run (Placement.placed (program (a := a)) placement) n
        (v.start (Placement.placed program placement)) = some c ∧
      step (Placement.placed program placement) c = none ∧ c.tapes = v ∧
      c.state = FiniteFlow.embed states 1 (selected (Counter.value rs) (Counter.value es)) := by
  obtain ⟨n,hn,hr,hh⟩ := selects (a := a) rs es
  have hrun : run (program (a := a)) n ((Placement.active placement v).start program) =
      some (result rs es) := by rw [ha]; exact hr
  refine ⟨n,hn,Placement.result placement v (result rs es),
    Placement.placed_run program placement v hrun,Placement.placed_halt program placement v hh,?_,rfl⟩
  rw [Placement.result_tapes]
  change Placement.replace placement v (input rs es) = v
  rw [← ha,Placement.replace_active]

/-- Exposed state test for integrating the selector into finite-flow control. -/
theorem selected_high_iff (r e : ℕ) : selected r e = high ↔ r < e := by
  unfold selected
  split_ifs <;> simp_all [high,fallback]

theorem selected_fallback_iff (r e : ℕ) : selected r e = fallback ↔ ¬(r < e) := by
  unfold selected
  split_ifs <;> simp_all [high,fallback]

end
end IntegerMultBounds.Machine.BinaryAdjacentWidthSelector.Less

namespace IntegerMultBounds.Machine.BinaryAdjacentWidthSelector
noncomputable section
variable {t a : ℕ}
open ArbitraryWidthHighBranchPlacement (placement active_input)

abbrev lessStates := Fintype.card (FiniteFlow.Control Less.states)
abbrev states : Fin 2 → ℕ := ![lessStates,lessStates]

def lessProgram (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag) :=
  Placement.placed (Less.program (a := a)) (placement left right flag hlr hlf hrf)

def family (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag) :
    (pc : Fin 2) → Program t (states pc) a :=
  Fin.cases (lessProgram left right flag hlr hlf hrf)
    (Fin.cases (lessProgram right left flag hlr.symm hrf hlf) (fun i => Fin.elim0 i))

def next : FiniteFlow.Next states :=
  Fin.cases (fun (st : Fin lessStates) => if st = FiniteFlow.embed Less.states 1 Less.high then none else some 1)
    (fun _ _ => none)

def program (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag) :=
  FiniteFlow.program (family (a := a) left right flag hlr hlf hrf) next 0

def cost (hs ds : List Bool) := Less.cost hs ds+1+Less.cost ds hs

def longDState := FiniteFlow.embed states 0 (FiniteFlow.embed Less.states 1 Less.high)
def longHState := FiniteFlow.embed states 1 (FiniteFlow.embed Less.states 1 Less.high)
def equalState := FiniteFlow.embed states 1 (FiniteFlow.embed Less.states 1 Less.fallback)
def selected (h d : ℕ) := if h < d then longDState else if d < h then longHState else equalState

private theorem less_states_ne :
    FiniteFlow.embed Less.states 1 Less.fallback ≠ FiniteFlow.embed Less.states 1 Less.high := by
  intro he
  have hh := (FiniteFlow.encoding Less.states).injective he
  have hv := congrArg (fun c : FiniteFlow.Control Less.states => c.2.val) hh
  change (2 : ℕ) = 1 at hv
  omega

private theorem longD_ne_longH : longDState ≠ longHState := by
  intro he
  have hh := (FiniteFlow.encoding states).injective he
  have hv := congrArg (fun c : FiniteFlow.Control states => c.1.val) hh
  change (0 : ℕ) = 1 at hv
  omega

private theorem longD_ne_equal : longDState ≠ equalState := by
  intro he
  have hh := (FiniteFlow.encoding states).injective he
  have hv := congrArg (fun c : FiniteFlow.Control states => c.1.val) hh
  change (0 : ℕ) = 1 at hv
  omega

private theorem equal_ne_longH : equalState ≠ longHState := by
  intro he
  have hh := (FiniteFlow.encoding states).injective he
  have hv := congrArg (fun c : FiniteFlow.Control states => c.2.val) hh
  exact less_states_ne (Fin.ext hv)

theorem selected_longD_iff (h d : ℕ) : selected h d = longDState ↔ h < d := by
  unfold selected
  split_ifs <;> simp_all [Ne.symm longD_ne_longH,Ne.symm longD_ne_equal]

theorem selected_longH_iff (h d : ℕ) : selected h d = longHState ↔ d < h := by
  unfold selected
  split_ifs <;> simp_all [longD_ne_longH,equal_ne_longH]
  omega

theorem selected_equal_iff (h d : ℕ) : selected h d = equalState ↔ h = d := by
  unfold selected
  split_ifs <;> simp_all [longD_ne_equal,Ne.symm equal_ne_longH]
  all_goals omega

/-- Two real comparisons reuse one flag. The first true outcome selects
long-D immediately; otherwise the swapped comparison selects long-H or equal.
Every terminal state has both original descriptor heads restored and a blank
flag. No branch label or comparison oracle is supplied. -/
theorem selects (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (v : Tapes t a) (hs ds : List Bool)
    (hht : v.tape left = BinaryDescriptorStack.descriptor hs) (hhh : v.head left = 1)
    (hdt : v.tape right = BinaryDescriptorStack.descriptor ds) (hdh : v.head right = 1)
    (hft : v.tape flag = fun _ => blank) (hfh : v.head flag = 0) :
    ∃ n ≤ cost hs ds, ∃ c,
      run (program left right flag hlr hlf hrf) n (v.start (program left right flag hlr hlf hrf)) = some c ∧
      step (program left right flag hlr hlf hrf) c = none ∧ c.tapes = v ∧
      c.state = selected (Counter.value hs) (Counter.value ds) := by
  obtain ⟨n,hn,c,hr,hh,ht,hstate⟩ := Less.selects_at
    (placement left right flag hlr hlf hrf) v hs ds
    (active_input left right flag hlr hlf hrf v hs ds hht hhh hdt hdh hft hfh)
  let fam := family (a := a) left right flag hlr hlf hrf
  by_cases hlt : Counter.value hs < Counter.value ds
  · have hedge : next 0 c.state = none := by
      change (if c.state = FiniteFlow.embed Less.states 1 Less.high then none else some 1) = none
      rw [hstate]
      simp [Less.selected,hlt]
    have htrace : FiniteFlow.Trace fam next 0 v n 0 c := .stop (family := fam) (next := next) 0 v n c hr hh hedge
    obtain ⟨hrr,hhh'⟩ := FiniteFlow.trace_run fam next 0 htrace
    refine ⟨n,by unfold cost; omega,c.mapState (FiniteFlow.embed states 0),hrr,hhh',ht,?_⟩
    change FiniteFlow.embed states 0 c.state = _
    rw [hstate]
    simp only [selected,Less.selected,ite_eq_left hlt,longDState]
  · obtain ⟨m,hm,d,hdr,hdhalt,hdtapes,hdstate⟩ := Less.selects_at
      (placement right left flag hlr.symm hrf hlf) v ds hs
      (active_input right left flag hlr.symm hrf hlf v ds hs hdt hdh hht hhh hft hfh)
    have hedge : next 0 c.state = some 1 := by
      change (if c.state = FiniteFlow.embed Less.states 1 Less.high then none else some 1) = some 1
      rw [hstate]
      simp only [Less.selected,ite_eq_right hlt,less_states_ne,ite_false]
    have htail : FiniteFlow.Trace fam next 1 c.tapes m 1 d := by
      rw [ht]
      exact .stop (family := fam) (next := next) 1 v m d hdr hdhalt rfl
    have htrace : FiniteFlow.Trace fam next 0 v (n+1+m) 1 d :=
      .join (family := fam) (next := next) 0 1 1 v n m c d hr hh hedge htail
    obtain ⟨hrr,hhh'⟩ := FiniteFlow.trace_run fam next 0 htrace
    refine ⟨n+1+m,by unfold cost; omega,d.mapState (FiniteFlow.embed states 1),hrr,hhh',hdtapes,?_⟩
    change FiniteFlow.embed states 1 d.state = _
    rw [hdstate]
    simp only [selected,ite_eq_right hlt,Less.selected]
    split_ifs <;> rfl

theorem preserves (left right flag : Fin t)
    (hlr : left ≠ right) (hlf : left ≠ flag) (hrf : right ≠ flag)
    (v : Tapes t a) (hs ds : List Bool)
    (hht : v.tape left = BinaryDescriptorStack.descriptor hs) (hhh : v.head left = 1)
    (hdt : v.tape right = BinaryDescriptorStack.descriptor ds) (hdh : v.head right = 1)
    (hft : v.tape flag = fun _ => blank) (hfh : v.head flag = 0) :
    HoareTime (program left right flag hlr hlf hrf) (fun w => w = v) (fun w => w = v) (cost hs ds) := by
  obtain ⟨n,hn,c,hr,hh,ht,_⟩ := selects left right flag hlr hlf hrf v hs ds hht hhh hdt hdh hft hfh
  rintro w rfl
  exact ⟨n,c,hn,hr,hh,ht⟩

theorem cost_volume (hs ds : List Bool)
    (hc : GrowingCounterData.Canonical hs) (dc : GrowingCounterData.Canonical ds)
    (V : ℕ) (hV : 0 < V) (hb : Counter.value hs ≤ V) (db : Counter.value ds ≤ V) :
    cost hs ds ≤ 43*V := by
  have h1 := Less.cost_volume hs ds hc dc V hV hb db
  have h2 := Less.cost_volume ds hs dc hc V hV db hb
  unfold cost
  omega

/-- Under the adjacent-width input condition the selected unequal branch has
exactly one extra bit, and the other descriptor is the shorter width. -/
theorem longH_adjacent (h d : ℕ) (hd : h ≤ d+1) (hs : selected h d = longHState) : h = d+1 := by
  have hh := (selected_longH_iff h d).mp hs
  omega

theorem longD_adjacent (h d : ℕ) (hd : d ≤ h+1) (hs : selected h d = longDState) : d = h+1 := by
  have hh := (selected_longD_iff h d).mp hs
  omega

end
end IntegerMultBounds.Machine.BinaryAdjacentWidthSelector
