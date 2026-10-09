import IntegerMultBounds.Machine.BinaryDescriptorCompare
import IntegerMultBounds.Machine.BinaryCanonicalData
import IntegerMultBounds.Machine.FiniteFlow
import IntegerMultBounds.Machine.Placement

/-! Paid manuscript guard 1 ≤ rho < e, read from the retained canonical
binary descriptors. The comparison flag is physically erased in the selecting
transition, and all descriptor cells and heads are restored. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighBranch
noncomputable section
variable {a : ℕ}

/-- Local tapes are rho, e, and one initially blank comparison flag. -/
abbrev input (rs es : List Bool) : Tapes 3 a := BinaryDescriptorCompare.input rs es

def high : Fin 3 := 1
def fallback : Fin 3 := 2

def selected (r e : ℕ) : Fin 3 := if 1 ≤ r ∧ r < e then high else fallback

def finish : Program 3 3 a where
  tapes_pos := by decide
  start := 0
  transition := fun st sy => if st = 0 then
    some (if sy 0 ≠ blank ∧ sy 2 = bitSymbol true then high else fallback,
      fun i => (if i = 2 then blank else sy i,Move.stay))
    else none

def cfg (v : Tapes 3 a) (st : Fin 3) : Config 3 3 a := ⟨st,v.head,v.tape⟩

/-- Canonical zero is the empty word; a noncanonical [false] is not silently
accepted as a positive exponent by this guard specification. -/
theorem descriptor_nonzero (rs : List Bool) (hc : GrowingCounterData.Canonical rs) :
    BinaryDescriptorStack.descriptor (a := a) rs 1 ≠ blank ↔ 1 ≤ Counter.value rs := by
  have hnil : BinaryDescriptorStack.descriptor (a := a) rs 1 = blank ↔ rs = [] := by
    cases rs with
    | nil => simp [BinaryDescriptorStack.descriptor,putWord,BinaryDescriptorStack.empty]
    | cons b bs => cases b <;> simp [BinaryDescriptorStack.descriptor,putWord,bitSymbol,blank,Fin.ext_iff]
  have hzero : Counter.value rs = 0 ↔ rs = [] := by
    constructor
    · exact BinaryCanonicalData.zero_nil rs hc
    · rintro rfl; rfl
  rw [ne_eq,hnil,← hzero]
  omega

theorem finish_test (rs es : List Bool) (hc : GrowingCounterData.Canonical rs) :
    ((BinaryDescriptorCompare.output (q := a) rs es).reads 0 ≠ blank ∧
      (BinaryDescriptorCompare.output (q := a) rs es).reads 2 = bitSymbol true) ↔
      1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es := by
  change (BinaryDescriptorStack.descriptor rs 1 ≠ blank ∧
    bitSymbol (a := a) (decide (Counter.value rs < Counter.value es)) = bitSymbol true) ↔ _
  rw [descriptor_nonzero rs hc]
  by_cases h : Counter.value rs < Counter.value es <;>
    simp [h,bitSymbol,Fin.ext_iff]

theorem finish_step (rs es : List Bool) (hc : GrowingCounterData.Canonical rs) :
    step (finish (a := a)) ((BinaryDescriptorCompare.output rs es).start finish) =
      some (cfg (input rs es) (selected (Counter.value rs) (Counter.value es))) := by
  have htest := finish_test (a := a) rs es hc
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

/-- The literal terminal finite state chooses the high-width branch exactly
when 1 ≤ rho < e. The flag and all scratch are blank at that boundary. -/
theorem selects (rs es : List Bool) (hc : GrowingCounterData.Canonical rs) :
    ∃ n ≤ cost rs es, run (program (a := a)) n ((input rs es).start program) = some (result rs es) ∧
      step (program (a := a)) (result rs es) = none := by
  obtain ⟨n,c,hn,hr,hh,hout⟩ := BinaryDescriptorCompare.compare_hoare (q := a) rs es _ rfl
  have hf := finish_step (a := a) rs es hc
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

theorem preserves (rs es : List Bool) (hc : GrowingCounterData.Canonical rs) :
    HoareTime (program (a := a)) (fun v => v = input rs es) (fun v => v = input rs es) (cost rs es) := by
  obtain ⟨n,hn,hr,hh⟩ := selects (a := a) rs es hc
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

/-- The explicit high/fallback terminal state remains visible when the three
local tapes are placed into any larger machine bank; all other tapes are
preserved without active-view assumptions in the postcondition. -/
theorem selects_at {t u : ℕ} (placement : Fin (3+u) ≃ Fin t) (v : Tapes t a)
    (rs es : List Bool) (hc : GrowingCounterData.Canonical rs)
    (ha : Placement.active placement v = input rs es) :
    ∃ n ≤ cost rs es, ∃ c,
      run (Placement.placed (program (a := a)) placement) n
        (v.start (Placement.placed program placement)) = some c ∧
      step (Placement.placed program placement) c = none ∧ c.tapes = v ∧
      c.state = FiniteFlow.embed states 1 (selected (Counter.value rs) (Counter.value es)) := by
  obtain ⟨n,hn,hr,hh⟩ := selects (a := a) rs es hc
  have hrun : run (program (a := a)) n ((Placement.active placement v).start program) =
      some (result rs es) := by rw [ha]; exact hr
  refine ⟨n,hn,Placement.result placement v (result rs es),
    Placement.placed_run program placement v hrun,Placement.placed_halt program placement v hh,?_,rfl⟩
  rw [Placement.result_tapes]
  change Placement.replace placement v (input rs es) = v
  rw [← ha,Placement.replace_active]

/-- Exposed state test for integrating the selector into finite-flow control. -/
theorem selected_high_iff (r e : ℕ) : selected r e = high ↔ 1 ≤ r ∧ r < e := by
  unfold selected
  split_ifs <;> simp_all [high,fallback]

theorem selected_fallback_iff (r e : ℕ) : selected r e = fallback ↔ ¬(1 ≤ r ∧ r < e) := by
  unfold selected
  split_ifs <;> simp_all [high,fallback]

end
end IntegerMultBounds.Machine.ArbitraryWidthHighBranch
