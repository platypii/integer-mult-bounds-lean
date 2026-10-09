import IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationSwap

/-! Real compact rotations for the four conjugations, padded into the same
bank as both physical interchange machines. No callback supplies a load. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationMiddle
noncomputable section
open ActivePrefixDirtyControlConjugationData
open ActivePrefixDirtyControlConjugationSwap (count bank middleBank)
open Networks.Shared50ModularControl (prime)

def focus (i : Fin 9) : Fin (17+swapCount) := Fin.castAdd swapCount (loadFocus i)
theorem focus_injective : Function.Injective focus := (Fin.castAdd_injective _ _).comp load_injective
def pureProgram := ActivePrefixDirtyControlLoadPlaced.program (a := prime) .pure focus focus_injective
def negativeProgram := ActivePrefixDirtyControlLoadPlaced.program (a := prime) .negative focus focus_injective
def unloadProgram := ActivePrefixDirtyControlNegativePureLoadPlaced.program (a := prime) focus focus_injective

theorem sources (l : LoadShape) (rows B : ℕ) (gs : Fin 7 → List Bool) (bw : List Bool)
    (hs : Fin 6 → List Bool) (rs bs : List Bool) (x : LoadArray l rows B) :
    SharedBank.payload (middleBank (base gs bw hs rs bs x)) focus=loadSources l rows B hs rs bs x := by
  change SharedBank.payload ((base gs bw hs rs bs x).append (SharedBank.empty swapCount prime))
    (fun i => Fin.castAdd swapCount (loadFocus i))=_
  rw [SharedBankFrames.payload_append_left,load_sources]

theorem output {m n : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool)
    (rs bs : List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    SharedPlacementAlphabet.setTape (middleBank (base gs bw hs rs bs x)) (focus 8) (ActiveTargetRotation.word y) 0=
      middleBank (base gs bw hs rs bs y) := by
  change SharedPlacementAlphabet.setTape ((base gs bw hs rs bs x).append (SharedBank.empty swapCount prime))
    (Fin.castAdd swapCount (16 : Fin 17)) _ 0=_
  rw [SharedPlacementAlphabet.setTape_append_left,base_set]
  rfl

def stateCount {t c : ℕ} (_ : Program t c prime) := c
def states : Kind → ℕ
  | .tPure | .uPure => stateCount pureProgram
  | .tNegative => stateCount negativeProgram
  | .uNegative => stateCount unloadProgram
def program : (kind : Kind) → Program count (states kind) prime
  | .tPure | .uPure => pureProgram
  | .tNegative => negativeProgram
  | .uNegative => unloadProgram

variable (l : LoadShape) (rows B : ℕ) (hrows : 0<rows) (hB : 0<B)
variable (habs : l.W+l.n*l.q+l.q+l.b+1≤2^(l.n*l.b)*B)
variable (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 6 → List Bool) (rs bs : List Bool)
variable (hv : ∀ i, Counter.value (hs i)=ActivePrefixDirtyControlData.values l i)
variable (hc : ∀ i, GrowingCounterData.Canonical (hs i))
variable (hr : Counter.value rs=rows) (cr : GrowingCounterData.Canonical rs)
variable (hb : Counter.value bs=B) (cb : GrowingCounterData.Canonical bs)
include hrows hB habs hv hc hr cr hb cb

theorem pure_runs (x : LoadArray l rows B) :
    HoareTime pureProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (loadResult .tPure l rows B x)))
      (ActivePrefixDirtyControlLoad.constant*ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B) := by
  have h := ActivePrefixDirtyControlLoadPlaced.runs (middleBank (base gs bw hs rs bs x)) focus focus_injective
    (m := .pure) l rows B hrows hB habs hs rs bs x (sources l rows B gs bw hs rs bs x)
    hv hc hr cr hb cb
  have he : ActivePrefixDirtyControlLoadPlaced.result (m := .pure) (middleBank (base gs bw hs rs bs x)) focus l rows B x=
      middleBank (base gs bw hs rs bs (loadResult .tPure l rows B x)) := output _ _ _ _ _ _ _
  rw [he] at h
  exact h

theorem negative_runs (x : LoadArray l rows B) :
    HoareTime negativeProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (loadResult .tNegative l rows B x)))
      (ActivePrefixDirtyControlLoad.constant*ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B) := by
  have hsrc : SharedBank.payload (middleBank (base gs bw hs rs bs x)) focus=
      ActivePrefixDirtyControlLoadPlaced.sources (m := .negative) l rows B hs rs bs x := by
    exact sources l rows B gs bw hs rs bs x
  have h := ActivePrefixDirtyControlLoadPlaced.runs (middleBank (base gs bw hs rs bs x)) focus focus_injective
    (m := .negative) l rows B hrows hB habs hs rs bs x hsrc hv hc hr cr hb cb
  have he : ActivePrefixDirtyControlLoadPlaced.result (m := .negative) (middleBank (base gs bw hs rs bs x)) focus l rows B x=
      middleBank (base gs bw hs rs bs (loadResult .tNegative l rows B x)) := output _ _ _ _ _ _ _
  rw [he] at h
  exact h

theorem unload_runs (x : LoadArray l rows B) :
    HoareTime unloadProgram (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (loadResult .uNegative l rows B x)))
      (ActivePrefixDirtyControlNegativePureLoad.constant*ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B) := by
  have hsrc : SharedBank.payload (middleBank (base gs bw hs rs bs x)) focus=
      ActivePrefixDirtyControlNegativePureLoadPlaced.sources l rows B hs rs bs x := by
    exact sources l rows B gs bw hs rs bs x
  have h := ActivePrefixDirtyControlNegativePureLoadPlaced.runs (middleBank (base gs bw hs rs bs x)) focus focus_injective
    l rows B hrows hB habs hs rs bs x hsrc hv hc hr cr hb cb
  have he : ActivePrefixDirtyControlNegativePureLoadPlaced.result (middleBank (base gs bw hs rs bs x)) focus l rows B x=
      middleBank (base gs bw hs rs bs (loadResult .uNegative l rows B x)) := output _ _ _ _ _ _ _
  rw [he] at h
  exact h

theorem runs (kind : Kind) (x : LoadArray l rows B) :
    HoareTime (program kind) (fun v => v=bank (base gs bw hs rs bs x))
      (fun v => v=bank (base gs bw hs rs bs (loadResult kind l rows B x)))
      (loadConstant kind*ActivePrefixDirtyControlLoadData.volume (m := .pure) l rows B) := by
  cases kind
  · exact pure_runs l rows B hrows hB habs gs bw hs rs bs hv hc hr cr hb cb x
  · exact negative_runs l rows B hrows hB habs gs bw hs rs bs hv hc hr cr hb cb x
  · exact pure_runs l rows B hrows hB habs gs bw hs rs bs hv hc hr cr hb cb x
  · exact unload_runs l rows B hrows hB habs gs bw hs rs bs hv hc hr cr hb cb x

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlConjugationMiddle
