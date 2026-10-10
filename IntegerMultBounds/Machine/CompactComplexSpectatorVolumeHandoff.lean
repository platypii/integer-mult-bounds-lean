import IntegerMultBounds.Machine.CompactComplexSpectatorVolumeHeaders

/-! Physical stream-volume setup, spectator promotion and exact cleanup. -/
namespace IntegerMultBounds.Machine.CompactComplexSpectatorVolumeHandoff
noncomputable section
open CompactGadgetReservationShape (Shape)
open ButterflyAxisHeadersArithmetic
open ActiveRepairRankHeadersCommands (State)
open CompactComplexNativeCodecFrame (bank)
open CompactSpectatorLeafSetup (raw)
open CompactComplexSpectatorVolumeHeaders
variable {s c : ℕ}

def program (headerCount : ℕ) (merge : Bool) (cur tar : Fin s) (hne : cur≠tar) (selected : Fin c) :=
  seq (seq (extend (headerProgram (s:=s) (c:=c) (CompactNativeRoleHeaders.schedule headerCount merge)) 10)
    (CompactComplexSpectatorTargetFamily.compile CompactComplexSpectatorTargetBank.roleSlot
      (CompactComplexSpectatorTargetBank.oldSlot cur) (CompactComplexSpectatorTargetBank.oldSlot tar)
      (CompactComplexSpectatorTargetBank.numericSlot (27:Fin 66))
      (CompactComplexSpectatorTargetBank.ports_injective cur tar hne 27)
      (CompactComplexSpectatorPromoteFamily.spectatorList selected)).2)
    (extend (headerProgram (s:=s) (c:=c) CompactNativeRoleHeaders.cleanup) 10)

/-- Paid volume setup, literal spectator promotion and exact header cleanup
give one actual raw-to-raw shared-grid handoff with no supplied length word
and no promotion relation. Both true denominator words remain retained. -/
theorem handoff_runs (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hc : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho : Fin sh.chunk) {left k levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left k levels frames returned)
    (dir : CompactSpectatorLeafGuardOriginal.Direction) (selected : Fin c)
    (before : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (p C n : ℕ) (hp : p≤metadataP-2*sh.bits)
    (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hwidth : ∀ role,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (before role))
    (hbefore : ∀ role,CompactSpectatorInheritedGrid.Grid sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) n (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) (before role))
    (cur tar : Fin s) (hne : cur≠tar)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2) (storage : Tapes s 2)
    (source : ℤ → Fin 6) (head : ℤ) (rawLeft rawCount slots right src dst : ℕ)
    (hcurrent : storage.head cur=1 ∧ storage.tape cur=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits n))
    (htarget : storage.head tar=1 ∧ storage.tape tar=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (n+CompactComplexRecursiveGeometry.arity^k))) :
    let rr := roleRows headerCount rows merge
    let q := metadataP-2*sh.bits
    let start := CompactComplexStoppedGridHandoff.childPayload sh rr ell q rho path.visit dir selected source head before
    let after := CompactComplexChildGridPromoted.aligned sh rr ell q rho path.visit dir selected before
    let old := raw sh rows ell metadataP rho.val rawLeft rawCount slots right src dst
    let prepared := CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho.val rawLeft rawCount slots right src dst
    ∃ time,
      HoareTime (program headerCount merge cur tar hne selected)
        (fun z => z=CompactComplexSpectatorTargetFamily.ready (bank control queue scalar old tail storage start))
        (fun z => z=CompactComplexSpectatorTargetFamily.ready
          (bank control queue scalar old tail storage
            (CompactComplexStoppedGridHandoff.payload sh rr ell source head after))) time ∧
      time≤scheduleCost (CompactNativeRoleHeaders.schedule headerCount merge) old+
        (CompactComplexSpectatorPromoteFamily.spectatorList selected).length*
          (130*streamVolume sh headerCount rows ell metadataP merge+8*(n+CompactComplexRecursiveGeometry.arity^k)+360)+
        scheduleCost CompactNativeRoleHeaders.cleanup prepared+2 ∧
      (∀ role,CompactSpectatorInheritedGrid.Grid sh rr ell q (n+CompactComplexRecursiveGeometry.arity^k)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)*4^(CompactComplexRecursiveGeometry.arity^k)) (after role)) ∧
      (∀ role,CompactSpectatorInheritedGrid.Grid sh rr ell q (n+CompactComplexRecursiveGeometry.arity^k)
        (CompactRecursiveGridBudget.bound p C levels (frames+2*(returned+CompactComplexRecursiveGeometry.arity^k))) (after role)) ∧
      (∀ role,role≠selected → CompactSpectatorInheritedGrid.decoded sh rr ell q
        (n+CompactComplexRecursiveGeometry.arity^k) (after role)=
          CompactSpectatorInheritedGrid.decoded sh rr ell q n (before role)) := by
  dsimp only
  let rr := roleRows headerCount rows merge
  let q := metadataP-2*sh.bits
  let start := CompactComplexStoppedGridHandoff.childPayload sh rr ell q rho path.visit dir selected source head before
  let after := CompactComplexChildGridPromoted.aligned sh rr ell q rho path.visit dir selected before
  have hrr : 0<rr := by cases merge <;> assumption
  have hprepare := hoare_extend_eq (prepare_runs sh headerCount rows ell metadataP rho.val rawLeft rawCount slots right src dst
    merge hc hr hgroup hG hA hK control queue scalar tail storage start) (SharedBank.empty 10 2)
  have hlength := prepared_length sh headerCount rows ell metadataP rho.val rawLeft rawCount slots right src dst
    merge control queue scalar tail storage start
  rw [volume_semantic sh headerCount rows ell metadataP merge hmetadata] at hlength
  obtain ⟨hhandoff,hgrid,hreturn,hvalues⟩ := CompactComplexStoppedGridHandoff.stopped_handoff sh rr ell q hrr rho path
    dir selected before p C n hp hchunk hwidth hbefore cur tar hne 27 control queue scalar
    (CompactNativeRoleHeaders.prepared headerCount merge sh rows ell metadataP rho.val rawLeft rawCount slots right src dst)
    tail storage source head hcurrent htarget hlength
  have hcleanup := hoare_extend_eq (cleanup_runs sh headerCount rows ell metadataP rho.val rawLeft rawCount slots right src dst
    merge control queue scalar tail storage (CompactComplexStoppedGridHandoff.payload sh rr ell source head after))
    (SharedBank.empty 10 2)
  have hrun := (hprepare.seq hhandoff).seq hcleanup
  refine ⟨_,hrun,?_,hgrid,hreturn,hvalues⟩
  rw [volume_semantic sh headerCount rows ell metadataP merge hmetadata]
  simp only [rr,q]
  omega

end
end IntegerMultBounds.Machine.CompactComplexSpectatorVolumeHandoff
