import IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalData

/-! Original-five-input highest-bit execution: construct every actual load
and swap descriptor, execute the complete physical action, erase every
constructed descriptor, and retain the literal original words and full array. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalRun
noncomputable section
open ActiveTargetHighestPairData ActiveTargetHighestPairHeadersData ActiveTargetHighestPairHeadersEndpoint
open ActiveTargetHighestPairOriginalData
open Networks.Shared50ModularControl (prime)

def prepareProgram := extend (extend (ActiveTargetHighestPairHeadersRun.program (a := prime)) 1)
  ActiveTargetHighestPairRun.count
def cleanupProgram := extend (extend (ActiveTargetHighestPairHeadersRun.cleanupProgram (a := prime)) 1)
  ActiveTargetHighestPairRun.count

def around {c : ℕ} (M : Program count c prime) := seq prepareProgram (seq M cleanupProgram)
def earlierProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  around (ActiveTargetHighestPairPlaced.earlierProgramFor m focus focus_injective)
def laterProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  around (ActiveTargetHighestPairPlaced.laterProgramFor m focus focus_injective)
def earlierProgram := earlierProgramFor .pure
def laterProgram := laterProgramFor .pure

def cost (g : Geometry) (middle : ℕ) := ActiveTargetHighestPairHeadersRun.cost g+middle+
  ActiveTargetHighestPairHeadersRun.cleanupCost g+2
def earlierCost (g : Geometry) := cost g (ActiveTargetHighestPairRun.earlierCost g)
def laterCost (g : Geometry) := cost g (ActiveTargetHighestPairRun.laterCost g (words g))

theorem prepares (g : Geometry) (hs : Fin 5 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime prepareProgram (fun v => v=bank (base hs x))
      (fun v => v=bank (prepared g x)) (ActiveTargetHighestPairHeadersRun.cost g) :=
  hoare_extend_eq (hoare_extend_eq (ActiveTargetHighestPairHeadersEndpoint.produces g hs hv hc)
    (arrayTape x)) (SharedBank.empty ActiveTargetHighestPairRun.count prime)

theorem cleans (g : Geometry) (hs : Fin 5 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime cleanupProgram (fun v => v=bank (prepared g x))
      (fun v => v=bank (base hs x)) (ActiveTargetHighestPairHeadersRun.cleanupCost g) :=
  hoare_extend_eq (hoare_extend_eq (ActiveTargetHighestPairHeadersEndpoint.cleans g hs hv hc)
    (arrayTape x)) (SharedBank.empty ActiveTargetHighestPairRun.count prime)

theorem around_runs {c budget : ℕ} (M : Program count c prime) (g : Geometry)
    (hs : Fin 5 → List Bool) (x y : Array g)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hm : HoareTime M (fun v => v=bank (prepared g x)) (fun v => v=bank (prepared g y)) budget) :
    HoareTime (around M) (fun v => v=bank (base hs x))
      (fun v => v=bank (base hs y)) (cost g budget) :=
  ((prepares g hs x hv hc).seq (hm.seq (cleans g hs y hv hc))).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem earlier_runs (g : Geometry) (hs : Fin 5 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*suffix g) :
    HoareTime earlierProgram (fun v => v=bank (base hs x))
      (fun v => v=bank (base hs (result g x))) (earlierCost g) := by
  have h := ActiveTargetHighestPairPlaced.earlier_runs (prepared g x) focus focus_injective
    g (words g) x (prepared_sources g x) (words_value g) (words_canonical g) habs
  rw [prepared_set] at h
  exact around_runs _ g hs x _ hv hc h

theorem later_runs_for (m : ActivePrefixDirtyControlLoadProducer.Mode) (g : Geometry)
    (hs : Fin 5 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (f : Array g → Array g)
    (hm : ∀ x,HoareTime (ActiveTargetHighestPairRun.loadProgram m)
      (fun w => w=ActiveTargetHighestPairRun.bank (caller (words g) x))
      (fun w => w=ActiveTargetHighestPairRun.bank (caller (words g) (f x)))
      (ActiveTargetHighestPairRun.earlierCost g)) :
    HoareTime (laterProgramFor m) (fun v => v=bank (base hs x))
      (fun v => v=bank (base hs (RadixRangePadding.transpose (f (RadixRangePadding.transpose x)))))
      (laterCost g) := by
  have h := ActiveTargetHighestPairPlaced.later_runs_for m (prepared g x) focus focus_injective
    g (words g) x (prepared_sources g x) (words_value g) (words_canonical g) f hm
  rw [prepared_set] at h
  exact around_runs _ g hs x _ hv hc h

theorem later_runs (g : Geometry) (hs : Fin 5 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*suffix g) :
    HoareTime laterProgram (fun v => v=bank (base hs x))
      (fun v => v=bank (base hs (later g x))) (laterCost g) :=
  later_runs_for .pure g hs x hv hc (result g)
    (fun x => ActiveTargetHighestPairRun.earlier_runs g (words g) x (words_value g) (words_canonical g) habs)

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalRun
