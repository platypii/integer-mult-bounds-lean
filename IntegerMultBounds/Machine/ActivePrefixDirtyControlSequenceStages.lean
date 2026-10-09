import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceData

/-! Six concrete original-input primitives on a single thirty-port bank.
Every target load and compact conjugation is a real paid machine call. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceStages
noncomputable section
open ActivePrefixDirtyControlSequenceData
open ActivePrefixDirtyControlConjugationData (FullArray view)
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)

abbrev conjugateCount := ActivePrefixDirtyControlConjugationSwap.count
def count := 30+conjugateCount+65
def middleBank (v : Tapes 30 prime) := CleanSubbank.bank (s := conjugateCount) v
def bank (v : Tapes 30 prime) := CleanSubbank.bank (s := 65) (middleBank v)
def liftedTarget (i : Fin 9) : Fin (30+conjugateCount) := Fin.castAdd conjugateCount (targetFocus i)
theorem lifted_injective : Function.Injective liftedTarget := (Fin.castAdd_injective _ _).comp target_injective

def selectedProgram := ActivePrefixDirtyControlLoadPlaced.program (a := prime) .selected liftedTarget lifted_injective
def correctionProgram := ActivePrefixDirtyControlLoadPlaced.program (a := prime) .correction liftedTarget lifted_injective
def tProgram (kind : ActivePrefixDirtyControlConjugationData.Kind) := extend
  (Placement.placed (ActivePrefixDirtyControlConjugationRun.tProgram kind)
    (CleanSubbank.placement ActivePrefixDirtyControlConjugationPlaced.ports compactFocus compact_injective)) 65
def uProgram (kind : ActivePrefixDirtyControlConjugationData.Kind) := extend
  (Placement.placed (ActivePrefixDirtyControlConjugationRun.uProgram kind)
    (CleanSubbank.placement ActivePrefixDirtyControlConjugationPlaced.ports sourceFocus source_injective)) 65
def pureProgram := tProgram .tPure
def negativeProgram := tProgram .tNegative
def loadProgram := uProgram .uPure
def unloadProgram := uProgram .uNegative

theorem target_payload {s : Shape} {g : Geometry s} (d : Inputs s g) (x : FullArray s g.rows) :
    SharedBank.payload (middleBank (caller d x)) liftedTarget=SharedBank.payload (caller d x) targetFocus :=
  SharedBankFrames.payload_append_left _ _ _

theorem target_set {s : Shape} {g : Geometry s} {m : ℕ} (d : Inputs s g) (x : FullArray s g.rows) (y : Fin m → Bool) :
    SharedPlacementAlphabet.setTape (middleBank (caller d x)) (liftedTarget 8)
      (ActiveTargetRotation.word y) 0=middleBank (caller d y) := by
  change SharedPlacementAlphabet.setTape ((caller d x).append (SharedBank.empty conjugateCount prime))
    (Fin.castAdd conjugateCount (29 : Fin 30)) _ 0=_
  rw [SharedPlacementAlphabet.setTape_append_left,caller_set]
  rfl

theorem bank_raw (v : Tapes 30 prime) : bank v=SharedBankStageInput.raw v count := by
  change (CleanSubbank.bank (s := conjugateCount) v).append (SharedBank.empty 65 prime)=_
  rw [SharedBankRawCompose.bank_eq_raw,SharedBankFamily.raw_append v (by omega)]
  rfl

variable {s : Shape} {g : Geometry s}

def targetCost (s : Shape) (rows : ℕ) := ActivePrefixDirtyControlLoad.constant*(rows*s.recordWidth)
def pureCost (s : Shape) (g : Geometry s) := ActivePrefixDirtyControlConjugationRun.cost .tPure s g.rows (g.n*g.b)
def negativeCost (s : Shape) (g : Geometry s) := ActivePrefixDirtyControlConjugationRun.cost .tNegative s g.rows (g.n*g.b)
def loadCost (s : Shape) (g : Geometry s) := ActivePrefixDirtyControlConjugationRun.cost .uPure s g.rows (g.n*g.b)
def unloadCost (s : Shape) (g : Geometry s) := ActivePrefixDirtyControlConjugationRun.cost .uNegative s g.rows (g.n*g.b)

theorem selected_runs (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime selectedProgram (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (selected g x))) (targetCost s g.rows) := by
  have h := ActivePrefixDirtyControlLoadPlaced.runs (middleBank (caller d x)) liftedTarget lifted_injective
    (m := .selected) g.target g.rows g.targetSuffix g.positiveRows g.positiveTargetSuffix g.targetAbsorbed
    d.ht d.rs d.bt (view g.targetVolume x) ((target_payload d x).trans (target_sources d x)) d.tv d.tc d.rv d.rc d.btv d.btc
  have he : ActivePrefixDirtyControlLoadPlaced.result (m := .selected) (middleBank (caller d x)) liftedTarget
      g.target g.rows g.targetSuffix (view g.targetVolume x)=middleBank (caller d (selected g x)) := by
    unfold ActivePrefixDirtyControlLoadPlaced.result
    rw [target_set]
    exact congrArg middleBank (caller_view g.targetVolume.symm d _).symm
  rw [he,←g.targetVolume] at h
  exact h

theorem correction_runs (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime correctionProgram (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (correction g x))) (targetCost s g.rows) := by
  have h := ActivePrefixDirtyControlLoadPlaced.runs (middleBank (caller d x)) liftedTarget lifted_injective
    (m := .correction) g.target g.rows g.targetSuffix g.positiveRows g.positiveTargetSuffix g.targetAbsorbed
    d.ht d.rs d.bt (view g.targetVolume x) ((target_payload d x).trans (target_sources d x)) d.tv d.tc d.rv d.rc d.btv d.btc
  have he : ActivePrefixDirtyControlLoadPlaced.result (m := .correction) (middleBank (caller d x)) liftedTarget
      g.target g.rows g.targetSuffix (view g.targetVolume x)=middleBank (caller d (correction g x)) := by
    unfold ActivePrefixDirtyControlLoadPlaced.result
    rw [target_set]
    exact congrArg middleBank (caller_view g.targetVolume.symm d _).symm
  rw [he] at h
  have hvol : ActivePrefixDirtyControlLoadData.volume (m := .correction) g.target g.rows g.targetSuffix=g.rows*s.recordWidth :=
    g.targetVolume.symm
  rw [hvol] at h
  exact h

def tResult (kind : ActivePrefixDirtyControlConjugationData.Kind) (g : Geometry s) (x : FullArray s g.rows) :=
  ActivePrefixDirtyControlConjugationRun.tResult kind s g.compact g.rows (g.n*g.b)
    g.compactSuffix g.compactFits g.compactVolume x
def tCost (kind : ActivePrefixDirtyControlConjugationData.Kind) (s : Shape) (g : Geometry s) :=
  ActivePrefixDirtyControlConjugationRun.tCost kind s g.rows (g.n*g.b)

theorem t_runs (kind : ActivePrefixDirtyControlConjugationData.Kind) (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime (tProgram kind) (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (tResult kind g x))) (tCost kind s g) := by
  have hn := ActivePrefixDirtyControlConjugationRun.t_runs kind s g.n g.rows g.b d.gs d.bw d.hc d.rs d.bc
    d.gv d.gc d.gb d.cb g.positiveWidth g.positiveRows g.positiveChunk g.positiveAxes g.positiveGuard
    g.positivePayload g.compactFits g.compact g.compactSuffix g.positiveCompactSuffix g.compactAbsorbed g.compactVolume
    d.cv d.cc d.rv d.rc d.bcv d.bcc x
  have h := ActivePrefixDirtyControlConjugationPlaced.realizes _ (caller d x) compactFocus compact_injective
    d.gs d.bw d.hc d.rs d.bc x _ (compact_sources d x) hn
  have he : ActivePrefixDirtyControlConjugationPlaced.result (caller d x) compactFocus
      (tResult kind g x)=caller d (tResult kind g x) := caller_set d x _
  dsimp only [tResult] at he
  rw [he] at h
  exact hoare_extend_eq h (SharedBank.empty 65 prime)

def uResult (kind : ActivePrefixDirtyControlConjugationData.Kind) (g : Geometry s) (x : FullArray s g.rows) :=
  ActivePrefixDirtyControlConjugationRun.uResult kind s g.source g.rows (g.n*g.b)
    g.compactSuffix g.compactFits g.sourceVolume x
def uCost (kind : ActivePrefixDirtyControlConjugationData.Kind) (s : Shape) (g : Geometry s) :=
  ActivePrefixDirtyControlConjugationRun.uCost kind s g.rows (g.n*g.b)

theorem u_runs (kind : ActivePrefixDirtyControlConjugationData.Kind) (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime (uProgram kind) (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (uResult kind g x))) (uCost kind s g) := by
  have hn := ActivePrefixDirtyControlConjugationRun.u_runs kind s g.n g.rows g.b d.gs d.bw d.hx d.rs d.bc
    d.gv d.gc d.gb d.cb g.positiveWidth g.positiveRows g.positiveChunk g.positiveAxes g.positiveGuard
    g.positivePayload g.compactFits g.source g.compactSuffix g.positiveCompactSuffix g.sourceAbsorbed g.sourceVolume
    d.xv d.xc d.rv d.rc d.bcv d.bcc x
  have h := ActivePrefixDirtyControlConjugationPlaced.realizes _ (caller d x) sourceFocus source_injective
    d.gs d.bw d.hx d.rs d.bc x _ (source_sources d x) hn
  have he : ActivePrefixDirtyControlConjugationPlaced.result (caller d x) sourceFocus
      (uResult kind g x)=caller d (uResult kind g x) := caller_set d x _
  dsimp only [uResult] at he
  rw [he] at h
  exact hoare_extend_eq h (SharedBank.empty 65 prime)

theorem pure_runs (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime pureProgram (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (pure g x))) (pureCost s g) := t_runs .tPure d x

theorem negative_runs (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime negativeProgram (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (negative g x))) (negativeCost s g) := t_runs .tNegative d x

theorem load_runs (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime loadProgram (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (load g x))) (loadCost s g) := u_runs .uPure d x

theorem unload_runs (d : Inputs s g) (x : FullArray s g.rows) :
    HoareTime unloadProgram (fun v => v=bank (caller d x))
      (fun v => v=bank (caller d (unload g x))) (unloadCost s g) := u_runs .uNegative d x

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceStages
