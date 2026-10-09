import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceBudget

/-! The complete prepared later-source schedule on arbitrary caller tapes.
All supplied numeric words and caller spectators survive; only the original
full array changes and every private tape returns blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequencePlaced
noncomputable section
open ActivePrefixDirtyControlSequenceData
open ActivePrefixDirtyControlSequenceStages (count bank)
open ActivePrefixDirtyControlConjugationData (FullArray)
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ} {s : Shape} {g : Geometry s}

def ports (i : Fin 30) : Fin count := ⟨i.val,by have := i.isLt; unfold count; omega⟩
theorem ports_injective : Function.Injective ports := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin count => k.val) h)

def programFor (a b c e : ActivePrefixDirtyControlConjugationData.Kind)
    (focus : Fin 30 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActivePrefixDirtyControlSequenceRun.programFor a b c e) (CleanSubbank.placement ports focus hf)
def program (focus : Fin 30 → Fin t) (hf : Function.Injective focus) := programFor .tPure .tNegative .uPure .uNegative focus hf
def result (v : Tapes t prime) (focus : Fin 30 → Fin t) (g : Geometry s) (x : FullArray s g.rows) :=
  setTape v (focus 29) (ActiveTargetRotation.word (later g x)) 0

theorem native_payload (v : Tapes 30 prime) : SharedBank.payload (bank v) ports=v := by
  rw [ActivePrefixDirtyControlSequenceStages.bank_raw]
  exact SharedBankRawCompose.payload_raw v ports (fun _ => rfl)
theorem native_clean (v : Tapes 30 prime) : SharedBank.strip (bank v) ports=SharedBank.empty count prime := by
  rw [ActivePrefixDirtyControlSequenceStages.bank_raw]
  exact SharedBankRawCompose.strip_raw v ports (fun _ => rfl)

theorem realizes {c budget : ℕ} (M : Program count c prime)
    (v : Tapes t prime) (focus : Fin 30 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s g) (x y : FullArray s g.rows) (hsrc : SharedBank.payload v focus=caller d x)
    (h : HoareTime M (fun w => w=bank (caller d x)) (fun w => w=bank (caller d y)) budget) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 29) (ActiveTargetRotation.word y) 0)) budget := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf v _
    _ _ _ ?_ ?_ (native_clean _) (native_clean _) ?_ h
  · exact (native_payload (caller d x)).trans hsrc.symm
  · refine (native_payload (caller d y)).trans ?_
    simp only [CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,caller_set]
  · simp only [CompactGadgetReservationPlacement.strip_set]

theorem runs_for (a b c e : ActivePrefixDirtyControlConjugationData.Kind)
    (v : Tapes t prime) (focus : Fin 30 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s g) (x : FullArray s g.rows) (hsrc : SharedBank.payload v focus=caller d x) :
    HoareTime (programFor a b c e focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (setTape v (focus 29)
        (ActiveTargetRotation.word (ActivePrefixDirtyControlSequenceRun.laterFor a b c e g x)) 0))
      (ActivePrefixDirtyControlSequenceRun.costFor a b c e s g) :=
  realizes _ v focus hf d x _ hsrc (ActivePrefixDirtyControlSequenceRun.runs_for a b c e d x)

theorem runs (v : Tapes t prime) (focus : Fin 30 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s g) (x : FullArray s g.rows) (hsrc : SharedBank.payload v focus=caller d x) :
    HoareTime (program focus hf) (fun w => w=CleanSubbank.bank (s := count) v)
      (fun w => w=CleanSubbank.bank (s := count) (result v focus g x))
      (ActivePrefixDirtyControlSequenceRun.cost s g) := runs_for .tPure .tNegative .uPure .uNegative v focus hf d x hsrc

theorem frame (v : Tapes t prime) (focus : Fin 30 → Fin t) (g : Geometry s) (x : FullArray s g.rows)
    (i : Fin t) (hi : i≠focus 29) :
    (result v focus g x).head i=v.head i ∧ (result v focus g x).tape i=v.tape i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequencePlaced
