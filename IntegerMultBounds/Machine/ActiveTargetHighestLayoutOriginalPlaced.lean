import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalRun

/-! Fifteen-port original-layout highest-bit execution on arbitrary caller banks.
The array alone changes; original fourteen words, caller spectators, and all private
blank tapes are retained exactly. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalPlaced
noncomputable section
open ActiveTargetHighestPairData
open ActivePrefixLayoutHeadersData (Inputs)
open ActiveTargetHighestLayoutHeadersData
open ActiveTargetHighestLayoutOriginalData
open ActiveTargetHighestPairOriginalData (arrayTape)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def basePorts : Fin 15 → Fin 44 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,43]
def ports (i : Fin 15) : Fin count := Fin.castAdd ActiveTargetHighestPairOriginalData.count (basePorts i)
theorem basePorts_injective : Function.Injective basePorts := by decide
theorem ports_injective : Function.Injective ports :=
  (Fin.castAdd_injective _ _).comp basePorts_injective

def sources {m : ℕ} (hs : Fin 14 → List Bool) (x : Fin m → Bool) : Tapes 15 prime :=
  (FixedHeaderBankCopy.headerBank hs).append (arrayTape x)

theorem sources_set {m n : ℕ} (hs : Fin 14 → List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (sources hs x) 14 (ActiveTargetRotation.word y) 0=sources hs y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_payload {m : ℕ} (hs : Fin 14 → List Bool) (x : Fin m → Bool) :
    SharedBank.payload (bank (base hs x)) ports=sources hs x := by
  change SharedBank.payload ((base hs x).append _) (fun i => Fin.castAdd _ (basePorts i))=_
  rw [SharedBankFrames.payload_append_left]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem base_clean {m : ℕ} (hs : Fin 14 → List Bool) (x : Fin m → Bool) :
    SharedBank.strip (base hs x) basePorts=SharedBank.empty 44 prime := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [basePorts,Fin.exists_fin_succ,base,
      ActivePrefixLayoutHeadersEndpoint.input,Tapes.append,SharedBank.empty] <;> rfl

theorem native_clean {m : ℕ} (hs : Fin 14 → List Bool) (x : Fin m → Bool) :
    SharedBank.strip (bank (base hs x)) ports=SharedBank.empty count prime := by
  change SharedBank.strip ((base hs x).append _) (fun i => Fin.castAdd _ (basePorts i))=_
  rw [SharedBankFrames.strip_append_left,base_clean,SharedBankFrames.empty_append]
  rfl

def earlierProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 15 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveTargetHighestLayoutOriginalRun.earlierProgramFor m)
    (CleanSubbank.placement ports focus hf)
def laterProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 15 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveTargetHighestLayoutOriginalRun.laterProgramFor m)
    (CleanSubbank.placement ports focus hf)
def earlierProgram (focus : Fin 15 → Fin t) (hf : Function.Injective focus) := earlierProgramFor .pure focus hf
def laterProgram (focus : Fin 15 → Fin t) (hf : Function.Injective focus) := laterProgramFor .pure focus hf

theorem realizes {c budget : ℕ} (M : Program count c prime)
    (v : Tapes t prime) (focus : Fin 15 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 14 → List Bool) (x y : Array g)
    (hsrc : SharedBank.payload v focus=sources hs x)
    (h : HoareTime M (fun w => w=bank (base hs x)) (fun w => w=bank (base hs y)) budget) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 14) (ActiveTargetRotation.word y) 0)) budget := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf v _
    _ _ _ ?_ ?_ (native_clean _ _) (native_clean _ _) ?_ h
  · exact (native_payload hs x).trans hsrc.symm
  · refine (native_payload hs y).trans ?_
    simp only [CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources_set]
  · simp only [CompactGadgetReservationPlacement.strip_set]

theorem earlier_runs (v : Tapes t prime) (focus : Fin 15 → Fin t) (hf : Function.Injective focus)
    (d : Inputs) (hvalid : Valid .early d) (g : Geometry)
    (hg : values .early d=ActiveTargetHighestPairHeadersData.originalValues g)
    (hs : Fin 14 → List Bool) (x : Array g)
    (hsrc : SharedBank.payload v focus=sources hs x)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*ActiveTargetHighestPairData.suffix g) :
    HoareTime (earlierProgram focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 14) (ActiveTargetRotation.word (result g x)) 0))
      (ActiveTargetHighestLayoutOriginalRun.earlierCost d g) :=
  realizes _ v focus hf g hs x _ hsrc (ActiveTargetHighestLayoutOriginalRun.earlier_runs d hvalid g hg hs x hv hc habs)

theorem later_runs_for (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (v : Tapes t prime) (focus : Fin 15 → Fin t) (hf : Function.Injective focus)
    (d : Inputs) (g : Geometry) (hs : Fin 14 → List Bool) (x y : Array g)
    (hsrc : SharedBank.payload v focus=sources hs x)
    (h : HoareTime (ActiveTargetHighestLayoutOriginalRun.laterProgramFor m)
      (fun w => w=bank (base hs x)) (fun w => w=bank (base hs y))
      (ActiveTargetHighestLayoutOriginalRun.laterCost d g)) :
    HoareTime (laterProgramFor m focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 14) (ActiveTargetRotation.word y) 0))
      (ActiveTargetHighestLayoutOriginalRun.laterCost d g) :=
  realizes _ v focus hf g hs x y hsrc h

theorem later_runs (v : Tapes t prime) (focus : Fin 15 → Fin t) (hf : Function.Injective focus)
    (d : Inputs) (hvalid : Valid .late d) (g : Geometry)
    (hg : values .late d=ActiveTargetHighestPairHeadersData.originalValues g)
    (hs : Fin 14 → List Bool) (x : Array g)
    (hsrc : SharedBank.payload v focus=sources hs x)
    (hv : ∀ i,Counter.value (hs i)=ActivePrefixLayoutHeadersData.originalValues d i)
    (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*ActiveTargetHighestPairData.suffix g) :
    HoareTime (laterProgram focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 14) (ActiveTargetRotation.word (later g x)) 0))
      (ActiveTargetHighestLayoutOriginalRun.laterCost d g) :=
  later_runs_for .pure v focus hf d g hs x _ hsrc (ActiveTargetHighestLayoutOriginalRun.later_runs d hvalid g hg hs x hv hc habs)

end
end IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalPlaced
