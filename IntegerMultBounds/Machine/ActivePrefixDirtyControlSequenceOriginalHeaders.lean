import IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalInputs

/-! Three actual dirty-control numeric header banks, followed by physical
cleanup that restores all generated metadata tapes to blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalHeaders
noncomputable section
open ActivePrefixDirtyControlSequenceOriginalData ActivePrefixDirtyControlSequenceOriginalInputs
open ActivePrefixEarlySequenceOriginalInputs (Inputs)
open ActivePrefixDirtyControlConjugationData (FullArray)
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}
variable (d : Inputs s p offset rows) (x : FullArray s rows)

def targetProgram := ActivePrefixDirtyControlHeadersPlaced.program (a := prime) .target targetFocus target_injective
def targetCleanup := ActivePrefixDirtyControlHeadersPlaced.cleanupProgram (a := prime) targetFocus target_injective

def compactProgram := ActivePrefixDirtyControlHeadersPlaced.program (a := prime) .compact compactFocus compact_injective
def compactCleanup := ActivePrefixDirtyControlHeadersPlaced.cleanupProgram (a := prime) compactFocus compact_injective

def sourceProgram := ActivePrefixDirtyControlHeadersPlaced.program (a := prime) .source sourceFocus source_injective
def sourceCleanup := ActivePrefixDirtyControlHeadersPlaced.cleanupProgram (a := prime) sourceFocus source_injective

theorem target_runs :
    HoareTime targetProgram (fun v => v=CleanSubbank.bank (s := 43) (base d.gs d.bw d.hs x))
      (fun v => v=CleanSubbank.bank (s := 43) (targetReady d.gs d.bw d.hs x (layout d)))
      (ActivePrefixDirtyControlHeadersRun.cost .target (layout d)) := by
  have h := ActivePrefixDirtyControlHeadersPlaced.produces (base d.gs d.bw d.hs x) targetFocus target_injective
    .target (layout d) p.compactFits d.hs (target_sources d.gs d.bw d.hs x none none) d.hv d.hc
  have he : ActivePrefixDirtyControlHeadersPlaced.result (base d.gs d.bw d.hs x) targetFocus .target (layout d)=(targetReady d.gs d.bw d.hs x (layout d)) := by
    apply installed_eq
    · exact target_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc none none
    · exact target_frame d.gs d.bw d.hs x none (some (targetWords (layout d))) none none
  rwa [he] at h

theorem target_cleans :
    HoareTime targetCleanup (fun v => v=CleanSubbank.bank (s := 43) (targetReady d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := 43) (base d.gs d.bw d.hs x))
      (ActivePrefixDirtyControlHeadersRun.cleanupCost .target (layout d)) := by
  have h := ActivePrefixDirtyControlHeadersPlaced.cleans (targetReady d.gs d.bw d.hs x (layout d)) targetFocus target_injective
    .target (layout d) d.hs (target_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc none none) d.hv d.hc
  have he : ActivePrefixDirtyControlHeadersPlaced.restored (targetReady d.gs d.bw d.hs x (layout d)) targetFocus d.hs=(base d.gs d.bw d.hs x) := by
    apply installed_eq
    · exact target_sources d.gs d.bw d.hs x none none
    · exact (target_frame d.gs d.bw d.hs x none (some (targetWords (layout d))) none none).symm
  rwa [he] at h

theorem compact_runs :
    HoareTime compactProgram (fun v => v=CleanSubbank.bank (s := 43) (targetReady d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := 43) (compactReady d.gs d.bw d.hs x (layout d)))
      (ActivePrefixDirtyControlHeadersRun.cost .compact (layout d)) := by
  have h := ActivePrefixDirtyControlHeadersPlaced.produces (targetReady d.gs d.bw d.hs x (layout d)) compactFocus compact_injective
    .compact (layout d) p.compactFits d.hs (compact_sources d.gs d.bw d.hs x (some (targetWords (layout d))) none) d.hv d.hc
  have he : ActivePrefixDirtyControlHeadersPlaced.result (targetReady d.gs d.bw d.hs x (layout d)) compactFocus .compact (layout d)=(compactReady d.gs d.bw d.hs x (layout d)) := by
    apply installed_eq
    · exact compact_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc (some (targetWords (layout d))) none
    · exact compact_frame d.gs d.bw d.hs x (some (targetWords (layout d))) none (some (compactWords (layout d))) none
  rwa [he] at h

theorem compact_cleans :
    HoareTime compactCleanup (fun v => v=CleanSubbank.bank (s := 43) (compactReady d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := 43) (targetReady d.gs d.bw d.hs x (layout d)))
      (ActivePrefixDirtyControlHeadersRun.cleanupCost .compact (layout d)) := by
  have h := ActivePrefixDirtyControlHeadersPlaced.cleans (compactReady d.gs d.bw d.hs x (layout d)) compactFocus compact_injective
    .compact (layout d) d.hs (compact_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc (some (targetWords (layout d))) none) d.hv d.hc
  have he : ActivePrefixDirtyControlHeadersPlaced.restored (compactReady d.gs d.bw d.hs x (layout d)) compactFocus d.hs=(targetReady d.gs d.bw d.hs x (layout d)) := by
    apply installed_eq
    · exact compact_sources d.gs d.bw d.hs x (some (targetWords (layout d))) none
    · exact (compact_frame d.gs d.bw d.hs x (some (targetWords (layout d))) none (some (compactWords (layout d))) none).symm
  rwa [he] at h

theorem source_runs :
    HoareTime sourceProgram (fun v => v=CleanSubbank.bank (s := 43) (compactReady d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := 43) (ready d.gs d.bw d.hs x (layout d)))
      (ActivePrefixDirtyControlHeadersRun.cost .source (layout d)) := by
  have h := ActivePrefixDirtyControlHeadersPlaced.produces (compactReady d.gs d.bw d.hs x (layout d)) sourceFocus source_injective
    .source (layout d) p.compactFits d.hs (source_sources d.gs d.bw d.hs x (some (targetWords (layout d))) (some (compactWords (layout d)))) d.hv d.hc
  have he : ActivePrefixDirtyControlHeadersPlaced.result (compactReady d.gs d.bw d.hs x (layout d)) sourceFocus .source (layout d)=(ready d.gs d.bw d.hs x (layout d)) := by
    apply installed_eq
    · exact source_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc (some (targetWords (layout d))) (some (compactWords (layout d)))
    · exact source_frame d.gs d.bw d.hs x (some (targetWords (layout d))) (some (compactWords (layout d))) none (some (sourceWords (layout d)))
  rwa [he] at h

theorem source_cleans :
    HoareTime sourceCleanup (fun v => v=CleanSubbank.bank (s := 43) (ready d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := 43) (compactReady d.gs d.bw d.hs x (layout d)))
      (ActivePrefixDirtyControlHeadersRun.cleanupCost .source (layout d)) := by
  have h := ActivePrefixDirtyControlHeadersPlaced.cleans (ready d.gs d.bw d.hs x (layout d)) sourceFocus source_injective
    .source (layout d) d.hs (source_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc (some (targetWords (layout d))) (some (compactWords (layout d)))) d.hv d.hc
  have he : ActivePrefixDirtyControlHeadersPlaced.restored (ready d.gs d.bw d.hs x (layout d)) sourceFocus d.hs=(compactReady d.gs d.bw d.hs x (layout d)) := by
    apply installed_eq
    · exact source_sources d.gs d.bw d.hs x (some (targetWords (layout d))) (some (compactWords (layout d)))
    · exact (source_frame d.gs d.bw d.hs x (some (targetWords (layout d))) (some (compactWords (layout d))) none (some (sourceWords (layout d)))).symm
  rwa [he] at h

end
end IntegerMultBounds.Machine.ActivePrefixDirtyControlSequenceOriginalHeaders
