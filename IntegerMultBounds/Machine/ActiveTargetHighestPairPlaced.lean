import IntegerMultBounds.Machine.ActiveTargetHighestPairSemantics

/-! Both actual highest-bit source orders run on arbitrary caller banks,
change only the array and preserve all original/prepared metadata. -/
namespace IntegerMultBounds.Machine.ActiveTargetHighestPairPlaced
noncomputable section
open ActiveTargetHighestPairData
open ActiveTargetHighestPairRun (count bank)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def ports (i : Fin 11) : Fin count := ⟨i.val,by have := i.isLt; unfold count; omega⟩
theorem ports_injective : Function.Injective ports := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin count => k.val) h)
def earlierProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) (focus : Fin 11 → Fin t)
    (hf : Function.Injective focus) := Placement.placed (ActiveTargetHighestPairRun.loadProgram m)
      (CleanSubbank.placement ports focus hf)
def laterProgramFor (m : ActivePrefixDirtyControlLoadProducer.Mode) (focus : Fin 11 → Fin t)
    (hf : Function.Injective focus) := Placement.placed (ActiveTargetHighestPairRun.programFor m)
      (CleanSubbank.placement ports focus hf)
def earlierProgram (focus : Fin 11 → Fin t) (hf : Function.Injective focus) := earlierProgramFor .pure focus hf
def laterProgram (focus : Fin 11 → Fin t) (hf : Function.Injective focus) := laterProgramFor .pure focus hf

theorem native_payload (v : Tapes 11 prime) : SharedBank.payload (bank v) ports=v := by
  rw [ActiveTargetHighestPairRun.bank_raw]
  exact SharedBankRawCompose.payload_raw v ports (fun _ => rfl)
theorem native_clean (v : Tapes 11 prime) : SharedBank.strip (bank v) ports=SharedBank.empty count prime := by
  rw [ActiveTargetHighestPairRun.bank_raw]
  exact SharedBankRawCompose.strip_raw v ports (fun _ => rfl)

theorem realizes {c budget : ℕ} (M : Program count c prime)
    (v : Tapes t prime) (focus : Fin 11 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 10 → List Bool) (x y : Array g)
    (hsrc : SharedBank.payload v focus=caller hs x)
    (h : HoareTime M (fun w => w=bank (caller hs x)) (fun w => w=bank (caller hs y)) budget) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 10) (ActiveTargetRotation.word y) 0)) budget := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf v _
    _ _ _ ?_ ?_ (native_clean _) (native_clean _) ?_ h
  · exact (native_payload (caller hs x)).trans hsrc.symm
  · refine (native_payload (caller hs y)).trans ?_
    simp only [CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,caller_set]
  · simp only [CompactGadgetReservationPlacement.strip_set]

theorem earlier_runs (v : Tapes t prime) (focus : Fin 11 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 10 → List Bool) (x : Array g)
    (hsrc : SharedBank.payload v focus=caller hs x)
    (hv : ∀ i,Counter.value (hs i)=values g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*suffix g) :
    HoareTime (earlierProgram focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 10) (ActiveTargetRotation.word (result g x)) 0))
      (ActiveTargetHighestPairRun.earlierCost g) :=
  realizes _ v focus hf g hs x _ hsrc (ActiveTargetHighestPairRun.earlier_runs g hs x hv hc habs)

theorem later_runs_for (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (v : Tapes t prime) (focus : Fin 11 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 10 → List Bool) (x : Array g)
    (hsrc : SharedBank.payload v focus=caller hs x)
    (hv : ∀ i,Counter.value (hs i)=values g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (f : Array g → Array g)
    (hm : ∀ x,HoareTime (ActiveTargetHighestPairRun.loadProgram m) (fun w => w=bank (caller hs x))
      (fun w => w=bank (caller hs (f x))) (ActiveTargetHighestPairRun.earlierCost g)) :
    HoareTime (laterProgramFor m focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 10)
        (ActiveTargetRotation.word (RadixRangePadding.transpose (f (RadixRangePadding.transpose x)))) 0))
      (ActiveTargetHighestPairRun.laterCost g hs) :=
  realizes _ v focus hf g hs x _ hsrc (ActiveTargetHighestPairRun.sandwich_runs m g hs hv hc f hm x)

theorem later_runs (v : Tapes t prime) (focus : Fin 11 → Fin t) (hf : Function.Injective focus)
    (g : Geometry) (hs : Fin 10 → List Bool) (x : Array g)
    (hsrc : SharedBank.payload v focus=caller hs x)
    (hv : ∀ i,Counter.value (hs i)=values g i) (hc : ∀ i,GrowingCounterData.Canonical (hs i))
    (habs : W g+6≤2*suffix g) :
    HoareTime (laterProgram focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 10) (ActiveTargetRotation.word (later g x)) 0))
      (ActiveTargetHighestPairRun.laterCost g hs) :=
  later_runs_for .pure v focus hf g hs x hsrc hv hc (result g)
    (fun x => ActiveTargetHighestPairRun.earlier_runs g hs x hv hc habs)

end
end IntegerMultBounds.Machine.ActiveTargetHighestPairPlaced
