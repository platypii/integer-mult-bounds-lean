import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalInputs

/-! The complete actual later sequence consumes the physically generated
header groups in the original 53-tape caller and preserves every spectator. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalPayload
noncomputable section
open ActivePrefixDirtyControlSequenceOriginalData ActivePrefixDirtyControlSequenceOriginalInputs
open ActivePrefixEarlySequenceOriginalInputs (Inputs)
open ActivePrefixDirtyControlConjugationData (FullArray)
open ActivePrefixLayoutShapes
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)

abbrev count := ActivePrefixDirtyControlSequenceStages.count
def programFor (a b c e : ActivePrefixDirtyControlConjugationData.Kind) :=
  ActivePrefixDirtyControlSequencePlaced.programFor a b c e sequenceFocus sequence_injective
def program := programFor .tPure .tNegative .uPure .uNegative
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem runs_for (a b c e : ActivePrefixDirtyControlConjugationData.Kind) (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (x : FullArray s rows) :
    HoareTime (programFor a b c e) (fun v => v=CleanSubbank.bank (s := count) (ready d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := count)
        (ready d.gs d.bw d.hs (ActivePrefixDirtyControlSequenceRun.laterFor a b c e (geometry hfit hn hb d) x) (layout d)))
      (ActivePrefixDirtyControlSequenceRun.costFor a b c e s (geometry hfit hn hb d)) := by
  have h := ActivePrefixDirtyControlSequencePlaced.runs_for a b c e (ready d.gs d.bw d.hs x (layout d))
    sequenceFocus sequence_injective (prepared hfit hn hb d) x (sequence_sources hfit hn hb d x)
  have he : SharedPlacementAlphabet.setTape (ready d.gs d.bw d.hs x (layout d))
      (sequenceFocus 29) (ActiveTargetRotation.word (ActivePrefixDirtyControlSequenceRun.laterFor a b c e (geometry hfit hn hb d) x)) 0=
      ready d.gs d.bw d.hs (ActivePrefixDirtyControlSequenceRun.laterFor a b c e (geometry hfit hn hb d) x) (layout d) := by
    exact state_set d.gs d.bw d.hs x _ _ _ _
  rwa [he] at h

theorem runs (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (d : Inputs s p offset rows) (x : FullArray s rows) :
    HoareTime program (fun v => v=CleanSubbank.bank (s := count) (ready d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := count)
        (ready d.gs d.bw d.hs (ActivePrefixDirtyControlSequenceData.later (geometry hfit hn hb d) x) (layout d)))
      (ActivePrefixDirtyControlSequenceRun.cost s (geometry hfit hn hb d)) :=
  runs_for .tPure .tNegative .uPure .uNegative hfit hn hb d x

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalPayload
