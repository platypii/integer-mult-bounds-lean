import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalData

/-! The actual highest-bit machine now accepts only original14 layout words.
Construction of both levels of headers, all scans and swaps, and all cleanup
are included in its charged runtime. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalRun
noncomputable section
open ActiveTargetHighestPairData
open ActiveTargetHighestLayoutHeadersData
open ActiveTargetHighestLayoutOriginalData
open ActivePrefixLayoutHeadersData (Inputs)
open ActiveTargetHighestPairOriginalData (arrayTape)
open Networks.Shared50ModularControl (prime)

def prepareProgram (mode : Mode) := extend (extend (ActiveTargetHighestLayoutHeadersRun.program (a := prime) mode) 1)
  ActiveTargetHighestPairOriginalData.count
def cleanupProgram := extend (extend (ActiveTargetHighestLayoutHeadersRun.cleanupProgram (a := prime)) 1)
  ActiveTargetHighestPairOriginalData.count

def around {c : ℕ} (mode : Mode) (M : Program count c prime) := seq (prepareProgram mode) (seq M cleanupProgram)
def earlierProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  around .early (ActiveTargetHighestPairOriginalPlaced.earlierProgramFor m focus focus_injective)
def laterProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) :=
  around .late (ActiveTargetHighestPairOriginalPlaced.laterProgramFor m focus focus_injective)
def earlierProgram := earlierProgramFor .pure
def laterProgram := laterProgramFor .pure

def cost (mode : Mode) (d : Inputs) (middle : ℕ) := ActiveTargetHighestLayoutHeadersRun.cost mode d+middle+
  ActiveTargetHighestLayoutHeadersRun.cleanupCost mode d+2
def earlierCost (d : Inputs) (g : Geometry) := cost .early d (ActiveTargetHighestPairOriginalRun.earlierCost g)
def laterCost (d : Inputs) (g : Geometry) := cost .late d (ActiveTargetHighestPairOriginalRun.laterCost g)

theorem prepares (mode : Mode) (d : Inputs) (hvalid : Valid mode d)
    (hs : Fin 14 → List Bool) {m : ℕ} (x : Fin m → Bool)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime (prepareProgram mode) (fun v => v=bank (base hs x))
      (fun v => v=bank (prepared mode d x)) (ActiveTargetHighestLayoutHeadersRun.cost mode d) := by
  have h := ActiveTargetHighestLayoutHeadersRun.runs (a := prime) mode d hvalid
  rw [←ActivePrefixLayoutHeadersEndpoint.input_eq d hs hv hc] at h
  exact hoare_extend_eq (hoare_extend_eq h (arrayTape x)) (SharedBank.empty ActiveTargetHighestPairOriginalData.count prime)

theorem cleans (mode : Mode) (d : Inputs) (hs : Fin 14 → List Bool) {m : ℕ} (x : Fin m → Bool)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i)) :
    HoareTime cleanupProgram (fun v => v=bank (prepared mode d x))
      (fun v => v=bank (base hs x)) (ActiveTargetHighestLayoutHeadersRun.cleanupCost mode d) := by
  have h := ActiveTargetHighestLayoutHeadersRun.cleans (a := prime) mode d
  rw [←ActivePrefixLayoutHeadersEndpoint.input_eq d hs hv hc] at h
  exact hoare_extend_eq (hoare_extend_eq h (arrayTape x)) (SharedBank.empty ActiveTargetHighestPairOriginalData.count prime)

theorem around_runs {c budget : ℕ} (mode : Mode) (M : Program count c prime) (d : Inputs)
    (hvalid : Valid mode d) (hs : Fin 14 → List Bool) {m : ℕ} (x y : Fin m → Bool)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hm : HoareTime M (fun v => v=bank (prepared mode d x))
      (fun v => v=bank (prepared mode d y)) budget) :
    HoareTime (around mode M) (fun v => v=bank (base hs x))
      (fun v => v=bank (base hs y)) (cost mode d budget) :=
  ((prepares mode d hvalid hs x hv hc).seq (hm.seq (cleans mode d hs y hv hc))).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

theorem earlier_runs (d : Inputs) (hvalid : Valid .early d) (g : Geometry)
    (hg : values .early d=ActiveTargetHighestPairHeadersData.originalValues g)
    (hs : Fin 14 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*ActiveTargetHighestPairData.suffix g) :
    HoareTime earlierProgram (fun v => v=bank (base hs x))
      (fun v => v=bank (base hs (result g x))) (earlierCost d g) := by
  have h := ActiveTargetHighestPairOriginalPlaced.earlier_runs (prepared .early d x) focus focus_injective
    g (words .early d) x (prepared_sources .early d x)
    (fun i => (words_value .early d i).trans (congrFun hg i)) (words_canonical .early d) habs
  rw [prepared_set] at h
  exact around_runs .early _ d hvalid hs x _ hv hc h

theorem later_runs_for (m : ActivePrefixDirtyControlLoadProducer.Mode) (d : Inputs)
    (hvalid : Valid .late d) (g : Geometry) (hs : Fin 14 → List Bool) (x y : Array g)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (hm : HoareTime (ActiveTargetHighestPairOriginalRun.laterProgramFor m)
      (fun v => v=ActiveTargetHighestPairOriginalData.bank (ActiveTargetHighestPairOriginalData.base (words .late d) x))
      (fun v => v=ActiveTargetHighestPairOriginalData.bank (ActiveTargetHighestPairOriginalData.base (words .late d) y))
      (ActiveTargetHighestPairOriginalRun.laterCost g)) :
    HoareTime (laterProgramFor m) (fun v => v=bank (base hs x))
      (fun v => v=bank (base hs y)) (laterCost d g) := by
  have h := ActiveTargetHighestPairOriginalPlaced.later_runs_for m (prepared .late d x) focus focus_injective
    g (words .late d) x y (prepared_sources .late d x) hm
  rw [prepared_set] at h
  exact around_runs .late _ d hvalid hs x y hv hc h

theorem later_runs (d : Inputs) (hvalid : Valid .late d) (g : Geometry)
    (hg : values .late d=ActiveTargetHighestPairHeadersData.originalValues g)
    (hs : Fin 14 → List Bool) (x : Array g)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*ActiveTargetHighestPairData.suffix g) :
    HoareTime laterProgram (fun v => v=bank (base hs x))
      (fun v => v=bank (base hs (later g x))) (laterCost d g) :=
  later_runs_for .pure d hvalid g hs x _ hv hc (ActiveTargetHighestPairOriginalRun.later_runs g (words .late d) x
    (fun i => (words_value .late d i).trans (congrFun hg i)) (words_canonical .late d) habs)

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalRun
