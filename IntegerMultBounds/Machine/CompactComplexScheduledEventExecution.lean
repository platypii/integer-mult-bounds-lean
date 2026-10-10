import IntegerMultBounds.Machine.CompactComplexCompletedLiveLower

/-! Finite local node execution composes actual named scalar lifecycles
and local child-machine contracts on one permanent caller bank. This compiler
does not implement the fixed cyclic recursive dispatcher. -/
namespace IntegerMultBounds.Machine.CompactComplexScheduledEventExecution
noncomputable section
open Networks
open CompactComplexCompletedLiveLower
open CompactComplexScalarIntegerRows (GroupIndex RowIndex)
open CompactComplexScalarSegmentRows (block)
open CompactComplexRecursiveLiveProgress (Live liveSlot)
attribute [local irreducible] Networks.ComplexRank25.program Networks.ComplexRecursiveCallSchema.calls
  Networks.ComplexFramedExecution.rows CompactComplexScalarSegmentRows.block
  CompactComplexCompletedLiveLower.schedule CompactComplexCompletedLiveLower.groups
  CompactComplexCompletedLiveLower.compileEvents
universe u
variable {s childTapes : ℕ}
open SharedBankStageInput (raw)
open CompactComplexScalarCountLifecycle (Realizes)
attribute [local irreducible] CompactComplexScalarCountLifecycle.program
  CompactComplexRolePhaseSite.roleCount

abbrev eventTapes (s childTapes : ℕ) := CompactComplexScalarCountLifecycle.totalTapes s+childTapes

private def padSigma {t N : ℕ} (P : Σ q,Program t q 2) (h : t≤N) : Σ q,Program N q 2 :=
  ⟨P.1,SharedBankFamily.padProgram P.2 h⟩

private theorem pad_sigma_runs {permanent t N : ℕ} (P : Σ q,Program t q 2) (ht : t≤N)
    (hp : permanent≤t) (before after : Tapes permanent 2) (cost : ℕ)
    (h : Realizes P before after cost) :
    HoareTime (padSigma P ht).2 (fun v => v=raw before N) (fun v => v=raw after N) cost :=
  SharedBankFamily.pad_realizes ht hp before after cost h


def localProgramsWith {t : ℕ}
    (scalar : GroupIndex → Σ q,Program t q 2)
    (child : ComplexRecursiveCallSchema.Call → Σ q,Program childTapes q 2) :
    Event → Σ q,Program (t+childTapes) q 2
  | .scalar g => padSigma (scalar g) (Nat.le_add_right _ _)
  | .child c => padSigma (child c) (Nat.le_add_left _ _)

/-- Finite local composition of fixed scalar and child machines. The local
contracts supply child execution; this theorem does not discharge recursion. -/
theorem scheduled_runsWith {X : Type u} {permanent t : ℕ}
    (scalar : GroupIndex → Σ q,Program t q 2)
    (child : ComplexRecursiveCallSchema.Call → Σ q,Program childTapes q 2)
    (hp : permanent≤t) (hchild : permanent≤childTapes) (slot : Fin permanent)
    (common : X → Tapes permanent 2)
    (next : Event → X → X) (cost : Event → X → ℕ) (exponent : X → ℕ) (d k : ℕ)
    (hscalarRuns : ∀ g x,Realizes (scalar g)
      (common x) (common (next (.scalar g) x)) (cost (.scalar g) x))
    (hchildRuns : ∀ c x,Realizes (child c)
      (common x) (common (next (.child c) x)) (cost (.child c) x))
    (hscalarExp : ∀ g x,exponent (next (.scalar g) x)=exponent x+(block g).length)
    (hchildExp : ∀ c x,exponent (next (.child c) x)=
      childTarget (ComplexRecursiveCallSchema.stopped d k) (exponent x) k)
    (hlive : ∀ x,Live (common x) slot (exponent x)) (x : X) :
    let ht : 0<t+childTapes := lt_of_lt_of_le
      (Nat.zero_lt_of_lt slot.isLt) (hp.trans (Nat.le_add_right _ _))
    let machines := localProgramsWith scalar child
    HoareTime (compileEvents ht machines schedule).2
      (fun v => v=raw (common x) (t+childTapes))
      (fun v => v=raw (common (runEvents next schedule x)) (t+childTapes) ∧
        Live v ⟨slot.val,lt_of_lt_of_le slot.isLt (hp.trans (Nat.le_add_right _ _))⟩
          (completed (ComplexRecursiveCallSchema.stopped d k) k schedule (exponent x)) ∧
        CompactComplexDenominatorPolicy.networkTarget (exponent x) k≤
          completed (ComplexRecursiveCallSchema.stopped d k) k schedule (exponent x))
      (runCost next cost schedule x) := by
  dsimp only
  have hlocal : ∀ e y,HoareTime (localProgramsWith scalar child e).2
      (fun v => v=raw (common y) (t+childTapes))
      (fun v => v=raw (common (next e y)) (t+childTapes)) (cost e y) := by
    intro e y
    cases e with
    | scalar g => exact pad_sigma_runs (scalar g) (Nat.le_add_right _ _) hp _ _ _ (hscalarRuns g y)
    | child c => exact pad_sigma_runs (child c) (Nat.le_add_left _ _) hchild _ _ _ (hchildRuns c y)
  have ht : 0<t+childTapes := lt_of_lt_of_le
    (Nat.zero_lt_of_lt slot.isLt) (hp.trans (Nat.le_add_right _ _))
  have hrun := compile_events_runs ht (localProgramsWith scalar child) common next cost hlocal schedule x
  apply hrun.consequence (fun _ h => h) _ le_rfl
  rintro v rfl
  refine ⟨rfl,?_,actual_network_target d k (exponent x)⟩
  have he := runEvents_exponent next exponent (ComplexRecursiveCallSchema.stopped d k) k
    hscalarExp hchildExp schedule x
  have hv := CompactComplexRecursiveLiveProgress.live_raw (common (runEvents next schedule x))
    slot (hp.trans (Nat.le_add_right t childTapes))
    (exponent (runEvents next schedule x)) (hlive _)
  rw [he] at hv
  exact hv

/-- Instantiate local event composition with the actual original-header scalar
lifecycle. Its primitive tape-count proof preserves the literal machine's sigma
state count without normalizing the fixed circuit during kernel conversion. -/
theorem scheduled_runs {X : Type u}
    (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (child : ComplexRecursiveCallSchema.Call → Σ q,Program childTapes q 2)
    (hchild : CompactComplexScalarCountLifecycle.publicTapes s≤childTapes)
    (common : X → Tapes (CompactComplexScalarCountLifecycle.publicTapes s) 2)
    (next : Event → X → X) (cost : Event → X → ℕ) (exponent : X → ℕ) (d k : ℕ)
    (hscalarRuns : ∀ g x,Realizes (CompactComplexScalarCountLifecycle.program hs header hh (block g))
      (common x) (common (next (.scalar g) x)) (cost (.scalar g) x))
    (hchildRuns : ∀ c x,Realizes (child c)
      (common x) (common (next (.child c) x)) (cost (.child c) x))
    (hscalarExp : ∀ g x,exponent (next (.scalar g) x)=exponent x+(block g).length)
    (hchildExp : ∀ c x,exponent (next (.child c) x)=
      childTarget (ComplexRecursiveCallSchema.stopped d k) (exponent x) k)
    (hlive : ∀ x,Live (common x) (liveSlot hs) (exponent x)) (x : X) :
    let hp : CompactComplexScalarCountLifecycle.publicTapes s≤
        (CompactComplexScalarCountLifecycle.publicTapes s+43+
          RawLinearCombinationComplexDenominatorPlaced.localCount CompactComplexScalarRowBlock.wireCount
            CompactComplexScalarPolynomialSequence.scratch) :=
      (Nat.le_add_right _ 43).trans (Nat.le_add_right _ _)
    let ht : 0<(CompactComplexScalarCountLifecycle.publicTapes s+43+
          RawLinearCombinationComplexDenominatorPlaced.localCount CompactComplexScalarRowBlock.wireCount
            CompactComplexScalarPolynomialSequence.scratch)+childTapes := lt_of_lt_of_le
      (Nat.zero_lt_of_lt (liveSlot hs).isLt) (hp.trans (Nat.le_add_right _ _))
    let machines := localProgramsWith
      (fun g => CompactComplexScalarCountLifecycle.program hs header hh (block g)) child
    HoareTime (compileEvents ht machines schedule).2
      (fun v => v=raw (common x) ((CompactComplexScalarCountLifecycle.publicTapes s+43+
          RawLinearCombinationComplexDenominatorPlaced.localCount CompactComplexScalarRowBlock.wireCount
            CompactComplexScalarPolynomialSequence.scratch)+childTapes))
      (fun v => v=raw (common (runEvents next schedule x)) ((CompactComplexScalarCountLifecycle.publicTapes s+43+
          RawLinearCombinationComplexDenominatorPlaced.localCount CompactComplexScalarRowBlock.wireCount
            CompactComplexScalarPolynomialSequence.scratch)+childTapes) ∧
        Live v ⟨(liveSlot hs).val,lt_of_lt_of_le (liveSlot hs).isLt
          (hp.trans (Nat.le_add_right _ _))⟩
          (completed (ComplexRecursiveCallSchema.stopped d k) k schedule (exponent x)) ∧
        CompactComplexDenominatorPolicy.networkTarget (exponent x) k≤
          completed (ComplexRecursiveCallSchema.stopped d k) k schedule (exponent x))
      (runCost next cost schedule x) :=
  scheduled_runsWith (fun g => CompactComplexScalarCountLifecycle.program hs header hh (block g)) child
    ((Nat.le_add_right (CompactComplexScalarCountLifecycle.publicTapes s) 43).trans
      (Nat.le_add_right _
        (RawLinearCombinationComplexDenominatorPlaced.localCount CompactComplexScalarRowBlock.wireCount
          CompactComplexScalarPolynomialSequence.scratch))) hchild (liveSlot hs)
    common next cost exponent d k hscalarRuns hchildRuns hscalarExp hchildExp hlive x

end
end IntegerMultBounds.Machine.CompactComplexScheduledEventExecution
