import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalInputs

/-! Both numeric header banks are actual producer outputs and are erased
physically after the four-load action, with all original words retained. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalHeaders
noncomputable section
open ActivePrefixEarlySequenceOriginalData ActivePrefixEarlySequenceOriginalInputs
open ActivePrefixEarlySequenceData (Array)
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open Networks.Shared50ModularControl (prime)

variable {s : Shape} {p : Parameters s} {offset rows : ℕ}
variable (hfit : offset+p.f*p.q≤p.before) (d : Inputs s p offset rows) (x : Array s rows)

def targetProgram := ActivePrefixLayoutHeadersPlaced.program (a := prime) .target targetFocus target_injective
def compactProgram := ActivePrefixLayoutHeadersPlaced.program (a := prime) .compactBefore compactFocus compact_injective
def targetCleanup := ActivePrefixLayoutHeadersPlaced.cleanupProgram (a := prime) targetFocus target_injective
def compactCleanup := ActivePrefixLayoutHeadersPlaced.cleanupProgram (a := prime) compactFocus compact_injective

include hfit in
theorem target_runs :
    HoareTime targetProgram (fun v => v=CleanSubbank.bank (s := 43) (base d.gs d.bw d.hs x))
      (fun v => v=CleanSubbank.bank (s := 43) (targetReady d.gs d.bw d.hs x (layout d)))
      (ActivePrefixLayoutHeadersBudget.constant*(rows*s.recordWidth)) := by
  have h := ActivePrefixLayoutHeadersLayout.produces .target (base d.gs d.bw d.hs x) targetFocus target_injective
    s p offset rows hfit d.hr d.hrecord d.hs (target_sources d.gs d.bw d.hs x) d.hv d.hc
  have he : ActivePrefixLayoutHeadersPlaced.result (base d.gs d.bw d.hs x) targetFocus .target (layout d)=
      targetReady d.gs d.bw d.hs x (layout d) := by
    apply installed_eq
    · exact target_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc none
    · exact target_frame d.gs d.bw d.hs x none (some (targetWords (layout d))) none
  dsimp only [layout,geometry] at he h ⊢
  rwa [he] at h

include hfit in
theorem compact_runs :
    HoareTime compactProgram (fun v => v=CleanSubbank.bank (s := 43) (targetReady d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := 43) (ready d.gs d.bw d.hs x (layout d)))
      (ActivePrefixLayoutHeadersBudget.constant*(rows*s.recordWidth)) := by
  have h := ActivePrefixLayoutHeadersLayout.produces .compactBefore (targetReady d.gs d.bw d.hs x (layout d))
    compactFocus compact_injective s p offset rows hfit d.hr d.hrecord d.hs
    (compact_sources d.gs d.bw d.hs x (layout d)) d.hv d.hc
  have he : ActivePrefixLayoutHeadersPlaced.result (targetReady d.gs d.bw d.hs x (layout d)) compactFocus .compactBefore (layout d)=
      ready d.gs d.bw d.hs x (layout d) := by
    apply installed_eq
    · exact compact_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc
    · exact compact_frame d.gs d.bw d.hs x (some (targetWords (layout d))) none (some (compactWords (layout d)))
  dsimp only [layout,geometry] at he h ⊢
  rwa [he] at h

include hfit in
theorem compact_cleans :
    HoareTime compactCleanup (fun v => v=CleanSubbank.bank (s := 43) (ready d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := 43) (targetReady d.gs d.bw d.hs x (layout d)))
      (ActivePrefixLayoutHeadersBudget.cleanupConstant*(rows*s.recordWidth)) := by
  have h := ActivePrefixLayoutHeadersLayout.cleans .compactBefore (ready d.gs d.bw d.hs x (layout d))
    compactFocus compact_injective s p offset rows hfit d.hr d.hrecord d.hs
    (compact_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc) d.hv d.hc
  have he : ActivePrefixLayoutHeadersPlaced.restored (ready d.gs d.bw d.hs x (layout d)) compactFocus d.hs=
      targetReady d.gs d.bw d.hs x (layout d) := by
    apply installed_eq
    · exact compact_sources d.gs d.bw d.hs x (layout d)
    · exact compact_frame d.gs d.bw d.hs x (some (targetWords (layout d))) (some (compactWords (layout d))) none
  dsimp only [layout,geometry] at he h ⊢
  rwa [he] at h

include hfit in
theorem target_cleans :
    HoareTime targetCleanup (fun v => v=CleanSubbank.bank (s := 43) (targetReady d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := 43) (base d.gs d.bw d.hs x))
      (ActivePrefixLayoutHeadersBudget.cleanupConstant*(rows*s.recordWidth)) := by
  have h := ActivePrefixLayoutHeadersLayout.cleans .target (targetReady d.gs d.bw d.hs x (layout d))
    targetFocus target_injective s p offset rows hfit d.hr d.hrecord d.hs
    (target_outputs d.gs d.bw d.hs x (layout d) d.hv d.hc none) d.hv d.hc
  have he : ActivePrefixLayoutHeadersPlaced.restored (targetReady d.gs d.bw d.hs x (layout d)) targetFocus d.hs=
      base d.gs d.bw d.hs x := by
    apply installed_eq
    · exact target_sources d.gs d.bw d.hs x
    · exact target_frame d.gs d.bw d.hs x (some (targetWords (layout d))) none none
  dsimp only [layout,geometry] at he h ⊢
  rwa [he] at h

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalHeaders
