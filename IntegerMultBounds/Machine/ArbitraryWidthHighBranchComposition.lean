import IntegerMultBounds.Machine.ArbitraryWidthHighBranchPlacement
import IntegerMultBounds.Machine.ArbitraryWidthHighGuard

/-! Genuine finite-state branching after the physical descriptor selector.
The branch programs and their Hoare contracts are explicit parameters; this
composition rule does not assert that a final wrapper has been instantiated. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighBranchComposition
noncomputable section
variable {t a h s : ℕ}

abbrev selectorStates := Fintype.card (FiniteFlow.Control ArbitraryWidthHighBranch.states)
abbrev states (h s : ℕ) : Fin 3 → ℕ := ![selectorStates,h,s]

def family (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag)
    (high : Program t h a) (fallback : Program t s a) :
    (pc : Fin 3) → Program t (states h s pc) a :=
  Fin.cases (ArbitraryWidthHighBranchPlacement.program rho width flag hrw hrf hwf)
    (Fin.cases high (Fin.cases fallback (fun i => Fin.elim0 i)))

def next : FiniteFlow.Next (states h s) :=
  Fin.cases (fun (st : Fin selectorStates) => if st = FiniteFlow.embed ArbitraryWidthHighBranch.states 1
      ArbitraryWidthHighBranch.high then some 1 else some 2)
    (Fin.cases (fun _ => none) (Fin.cases (fun _ => none) (fun i => Fin.elim0 i)))

def program (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag)
    (high : Program t h a) (fallback : Program t s a) :=
  FiniteFlow.program (family rho width flag hrw hrf hwf high fallback) next 0

theorem selected_high_iff (r e : ℕ) :
    ArbitraryWidthHighBranch.selected r e = ArbitraryWidthHighBranch.high ↔ 1 ≤ r ∧ r < e :=
  ArbitraryWidthHighBranch.selected_high_iff r e

theorem selected_fallback_iff (r e : ℕ) :
    ArbitraryWidthHighBranch.selected r e = ArbitraryWidthHighBranch.fallback ↔ ¬(1 ≤ r ∧ r < e) :=
  ArbitraryWidthHighBranch.selected_fallback_iff r e

private theorem embed_ne :
    FiniteFlow.embed ArbitraryWidthHighBranch.states 1 ArbitraryWidthHighBranch.fallback ≠
      FiniteFlow.embed ArbitraryWidthHighBranch.states 1 ArbitraryWidthHighBranch.high := by
  intro he
  have hh := (FiniteFlow.encoding ArbitraryWidthHighBranch.states).injective he
  have hv := congrArg (fun c : FiniteFlow.Control ArbitraryWidthHighBranch.states => c.2.val) hh
  change (2 : ℕ) = 1 at hv
  omega

theorem next_selected (r e : ℕ) :
    next (h := h) (s := s) 0
      (FiniteFlow.embed ArbitraryWidthHighBranch.states 1 (ArbitraryWidthHighBranch.selected r e)) =
      some (if 1 ≤ r ∧ r < e then 1 else 2) := by
  change (if FiniteFlow.embed ArbitraryWidthHighBranch.states 1
    (ArbitraryWidthHighBranch.selected r e) =
    FiniteFlow.embed ArbitraryWidthHighBranch.states 1 ArbitraryWidthHighBranch.high
    then some 1 else some 2) = _
  by_cases hg : 1 ≤ r ∧ r < e
  · rw [ite_eq_left hg]
    simp only [ArbitraryWidthHighBranch.selected,ite_eq_left hg,ite_true]
  · rw [ite_eq_right hg]
    simp only [ArbitraryWidthHighBranch.selected,ite_eq_right hg,embed_ne,ite_false]

/-- The actual selector restores every tape/head and erases the comparison
flag before its terminal finite state chooses the supplied branch program.
The selector-to-branch jump costs one real transition; the chosen branch's
terminal state is a genuine halt of the complete finite-flow machine. -/
theorem runs (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag)
    (high : Program t h a) (fallback : Program t s a)
    (v highOut fallbackOut : Tapes t a) (highCost fallbackCost : ℕ)
    (rs es : List Bool) (cr : GrowingCounterData.Canonical rs)
    (hrr : v.tape rho = BinaryDescriptorStack.descriptor rs) (hrh : v.head rho = 1)
    (her : v.tape width = BinaryDescriptorStack.descriptor es) (heh : v.head width = 1)
    (hfr : v.tape flag = fun _ => blank) (hfh : v.head flag = 0)
    (highRuns : (1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es) →
      HoareTime high (fun w => w = v) (fun w => w = highOut) highCost)
    (fallbackRuns : ¬(1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es) →
      HoareTime fallback (fun w => w = v) (fun w => w = fallbackOut) fallbackCost) :
    HoareTime (program rho width flag hrw hrf hwf high fallback)
      (fun w => w = v)
      (fun w => w = if 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es
        then highOut else fallbackOut)
      (ArbitraryWidthHighBranch.cost rs es+1+
        if 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es then highCost else fallbackCost) := by
  obtain ⟨n,hn,c,hr,hh,ht,hstate⟩ :=
    ArbitraryWidthHighBranchPlacement.selects rho width flag hrw hrf hwf v rs es cr
      hrr hrh her heh hfr hfh
  let fam := family rho width flag hrw hrf hwf high fallback
  by_cases hg : 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es
  · obtain ⟨m,d,hm,hdr,hdh,hdout⟩ := highRuns hg v rfl
    have htail : FiniteFlow.Trace fam next 1 c.tapes m 1 d := by
      rw [ht]
      exact .stop (family := fam) (next := next) 1 v m d hdr hdh rfl
    have hedge : next (h := h) (s := s) 0 c.state = some 1 := by
      rw [hstate,next_selected]
      simp [hg]
    have htrace : FiniteFlow.Trace fam next 0 v (n+1+m) 1 d :=
      .join (family := fam) (next := next) 0 1 1 v n m c d hr hh hedge htail
    have hc := FiniteFlow.trace_hoare fam next htrace
    apply hc.consequence (fun _ hv => hv) _ _
    · intro w hw
      have hout : d.tapes = if 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es
          then highOut else fallbackOut := by
        rw [ite_eq_left hg]
        exact hdout
      exact hw.trans hout
    · rw [ite_eq_left hg]
      omega
  · obtain ⟨m,d,hm,hdr,hdh,hdout⟩ := fallbackRuns hg v rfl
    have htail : FiniteFlow.Trace fam next 2 c.tapes m 2 d := by
      rw [ht]
      exact .stop (family := fam) (next := next) 2 v m d hdr hdh rfl
    have hedge : next (h := h) (s := s) 0 c.state = some 2 := by
      rw [hstate,next_selected]
      simp [hg]
    have htrace : FiniteFlow.Trace fam next 0 v (n+1+m) 2 d :=
      .join (family := fam) (next := next) 0 2 2 v n m c d hr hh hedge htail
    have hc := FiniteFlow.trace_hoare fam next htrace
    apply hc.consequence (fun _ hv => hv) _ _
    · intro w hw
      have hout : d.tapes = if 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es
          then highOut else fallbackOut := by
        rw [ite_eq_right hg]
        exact hdout
      exact hw.trans hout
    · rw [ite_eq_right hg]
      omega

/-- Common-output form for two implementations of the same operation. Both
canonical descriptor lengths are absorbed in the caller's positive volume;
all branch runtime charges remain explicit. -/
theorem runs_same_volume (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag)
    (high : Program t h a) (fallback : Program t s a)
    (v out : Tapes t a) (highCost fallbackCost V : ℕ) (hV : 0 < V)
    (rs es : List Bool) (cr : GrowingCounterData.Canonical rs) (ce : GrowingCounterData.Canonical es)
    (hrV : Counter.value rs ≤ V) (heV : Counter.value es ≤ V)
    (hrr : v.tape rho = BinaryDescriptorStack.descriptor rs) (hrh : v.head rho = 1)
    (her : v.tape width = BinaryDescriptorStack.descriptor es) (heh : v.head width = 1)
    (hfr : v.tape flag = fun _ => blank) (hfh : v.head flag = 0)
    (highRuns : (1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es) →
      HoareTime high (fun w => w = v) (fun w => w = out) highCost)
    (fallbackRuns : ¬(1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es) →
      HoareTime fallback (fun w => w = v) (fun w => w = out) fallbackCost) :
    HoareTime (program rho width flag hrw hrf hwf high fallback)
      (fun w => w = v) (fun w => w = out)
      (21*V+1+if 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es
        then highCost else fallbackCost) := by
  have hh := runs rho width flag hrw hrf hwf high fallback v out out highCost fallbackCost
    rs es cr hrr hrh her heh hfr hfh highRuns fallbackRuns
  have hb := ArbitraryWidthHighBranch.cost_volume rs es cr ce V hV hrV heV
  apply hh.consequence (fun _ h => h) _ _
  · intro w hw
    simpa only [ite_self] using hw
  · omega

/-- When rho is the actual high-depth selector, the physical fallback state
can occur only in a fixed finite set of widths. No algorithm for choosing the
mathematical cutoff is assumed here. -/
theorem bounded_fallback (q : ℕ) (hq : 2 ≤ q) :
    ∃ cutoff : ℕ, ∀ e : ℕ,
      ArbitraryWidthHighBranch.selected (ArbitraryWidthHighPrepare.highDepth q e) e =
        ArbitraryWidthHighBranch.fallback → e < cutoff := by
  obtain ⟨cutoff,hcut⟩ := ArbitraryWidthHighGuard.bounded_fallback q hq
  refine ⟨cutoff,?_⟩
  intro e he
  have hnot := (selected_fallback_iff _ _).mp he
  by_contra hlt
  exact hnot (hcut e (by omega))

/-- Equivalent finite-width bound stated directly in terms of the enclosing
finite-control edge, after the actual selector's terminal state is observed. -/
theorem bounded_fallback_edge (q : ℕ) (hq : 2 ≤ q) :
    ∃ cutoff : ℕ, ∀ e : ℕ,
      next (h := h) (s := s) 0 (FiniteFlow.embed ArbitraryWidthHighBranch.states 1
        (ArbitraryWidthHighBranch.selected (ArbitraryWidthHighPrepare.highDepth q e) e)) = some 2 →
      e < cutoff := by
  obtain ⟨cutoff,hcut⟩ := bounded_fallback q hq
  refine ⟨cutoff,?_⟩
  intro e he
  apply hcut e
  apply (selected_fallback_iff _ _).mpr
  intro hg
  rw [next_selected] at he
  simp [hg] at he

end
end IntegerMultBounds.Machine.ArbitraryWidthHighBranchComposition
