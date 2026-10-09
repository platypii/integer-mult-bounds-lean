import IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalRun

/-! Six-port original-header highest-bit execution on arbitrary caller banks.
The array alone changes; original words, caller spectators, and all private
blank tapes are retained exactly. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalPlaced
noncomputable section
open ActiveTargetHighestPairData ActiveTargetHighestPairHeadersData
open ActiveTargetHighestPairOriginalData
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def basePorts : Fin 6 → Fin 44 := ![0,1,2,3,4,43]
def ports (i : Fin 6) : Fin count := Fin.castAdd ActiveTargetHighestPairRun.count (basePorts i)
theorem basePorts_injective : Function.Injective basePorts := by decide
theorem ports_injective : Function.Injective ports :=
  (Fin.castAdd_injective _ _).comp basePorts_injective

def sources {m : ℕ} (hs : Fin 5 → List Bool) (x : Fin m → Bool) : Tapes 6 prime :=
  (FixedHeaderBankCopy.headerBank hs).append (arrayTape x)

theorem sources_set {m n : ℕ} (hs : Fin 5 → List Bool) (x : Fin m → Bool) (y : Fin n → Bool) :
    setTape (sources hs x) 5 (ActiveTargetRotation.word y) 0=sources hs y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_payload {m : ℕ} (hs : Fin 5 → List Bool) (x : Fin m → Bool) :
    SharedBank.payload (bank (base hs x)) ports=sources hs x := by
  change SharedBank.payload ((base hs x).append _) (fun i => Fin.castAdd _ (basePorts i))=_
  rw [SharedBankFrames.payload_append_left]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem base_clean {m : ℕ} (hs : Fin 5 → List Bool) (x : Fin m → Bool) :
    SharedBank.strip (base hs x) basePorts=SharedBank.empty 44 prime := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
    simp [basePorts,Fin.exists_fin_succ,base,
      ActiveTargetHighestPairHeadersEndpoint.input,Tapes.append,SharedBank.empty] <;> rfl

theorem native_clean {m : ℕ} (hs : Fin 5 → List Bool) (x : Fin m → Bool) :
    SharedBank.strip (bank (base hs x)) ports=SharedBank.empty count prime := by
  change SharedBank.strip ((base hs x).append _) (fun i => Fin.castAdd _ (basePorts i))=_
  rw [SharedBankFrames.strip_append_left,base_clean,SharedBankFrames.empty_append]
  rfl

def earlierProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 6 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveTargetHighestPairOriginalRun.earlierProgramFor m)
    (CleanSubbank.placement ports focus hf)
def laterProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 6 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveTargetHighestPairOriginalRun.laterProgramFor m)
    (CleanSubbank.placement ports focus hf)
def earlierProgram (focus : Fin 6 → Fin t) (hf : Function.Injective focus) := earlierProgramFor .pure focus hf
def laterProgram (focus : Fin 6 → Fin t) (hf : Function.Injective focus) := laterProgramFor .pure focus hf

theorem realizes {c budget : ℕ} (M : Program count c prime)
    (v : Tapes t prime) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 5 → List Bool) (x y : Array g)
    (hsrc : SharedBank.payload v focus=sources hs x)
    (h : HoareTime M (fun w => w=bank (base hs x)) (fun w => w=bank (base hs y)) budget) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 5) (ActiveTargetRotation.word y) 0)) budget := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf v _
    _ _ _ ?_ ?_ (native_clean _ _) (native_clean _ _) ?_ h
  · exact (native_payload hs x).trans hsrc.symm
  · refine (native_payload hs y).trans ?_
    simp only [CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,sources_set]
  · simp only [CompactGadgetReservationPlacement.strip_set]

theorem earlier_runs (v : Tapes t prime) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 5 → List Bool) (x : Array g)
    (hsrc : SharedBank.payload v focus=sources hs x)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*suffix g) :
    HoareTime (earlierProgram focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 5) (ActiveTargetRotation.word (result g x)) 0))
      (ActiveTargetHighestPairOriginalRun.earlierCost g) :=
  realizes _ v focus hf g hs x _ hsrc (ActiveTargetHighestPairOriginalRun.earlier_runs g hs x hv hc habs)

theorem later_runs_for (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (v : Tapes t prime) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 5 → List Bool) (x y : Array g)
    (hsrc : SharedBank.payload v focus=sources hs x)
    (h : HoareTime (ActiveTargetHighestPairOriginalRun.laterProgramFor m)
      (fun w => w=bank (base hs x)) (fun w => w=bank (base hs y))
      (ActiveTargetHighestPairOriginalRun.laterCost g)) :
    HoareTime (laterProgramFor m focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 5) (ActiveTargetRotation.word y) 0))
      (ActiveTargetHighestPairOriginalRun.laterCost g) :=
  realizes _ v focus hf g hs x y hsrc h

theorem later_runs (v : Tapes t prime) (focus : Fin 6 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 5 → List Bool) (x : Array g)
    (hsrc : SharedBank.payload v focus=sources hs x)
    (hv : ∀ i,Counter.value (hs i)=originalValues g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*suffix g) :
    HoareTime (laterProgram focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 5) (ActiveTargetRotation.word (later g x)) 0))
      (ActiveTargetHighestPairOriginalRun.laterCost g) :=
  later_runs_for .pure v focus hf g hs x _ hsrc (ActiveTargetHighestPairOriginalRun.later_runs g hs x hv hc habs)

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairOriginalPlaced
