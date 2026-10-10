import IntegerMultBounds.Machine.CompactNativeRoleRecombine
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal
import IntegerMultBounds.Machine.CompactComplexSourceReadyPrefixGeometry

/-! Corrected actual role families directly supply current-node contraction
and row-major rejoining. The common whole array, widths and physical role words
are derived internally; exact contraction retains the original Path reserve. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRoleRejoin
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactNativeRoleRecombine (recombine)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
open CompactRecursiveDependencyBudget (Path)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyNonleafFinalPath.program
  CompactComplexSourceReadyNonleafOrientedFinal.program

def payload {sh : Shape} {rows ell : ℕ} (data : Fin c → Array sh rows ell) : Tapes (1+c) 2 :=
  CyclicRowCopy.payload (fun _ => blank)
    (fun j => NativeZeroPadding.word (NativeZeroPaddingArray.word (data j))) 0 (fun _ => 0)

theorem payload_source {sh : Shape} {rows ell : ℕ} (data : Fin c → Array sh rows ell) :
    (payload data).head 0=0 ∧ (payload data).tape 0=fun _ => blank := by
  simp only [payload,CyclicRowCopy.payload,Tapes.append]
  exact ⟨rfl,rfl⟩

theorem payload_roles (sh : Shape) (rows ell : ℕ) (hd : c ∣ rows)
    (data : Fin c → Array sh (rows/c) ell) :
    ∀ j,(payload data).head (Fin.natAdd 1 j)=0 ∧
      (payload data).tape (Fin.natAdd 1 j)=NativeSignedGapReturn.word
        (CompactComplexStoppedGridHandoff.words
          (CompactNativeRoleReservedBridge.role sh rows c ell hd (recombine sh rows c ell hd data) j)) := by
  intro j
  rw [CompactNativeRoleRecombine.role_recombine,CompactComplexSourceReadyNonleafFinalGeometry.words_tape]
  simp only [payload,CyclicRowCopy.payload,Tapes.append,Fin.addCases_right,and_self]

/-- The required original split representation is derived from the complete
family, rather than assumed as a physical input-codec equality. -/
theorem payload_recombine (sh : Shape) (rows ell : ℕ) (hd : c ∣ rows)
    (data : Fin c → Array sh (rows/c) ell) :
    CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd (recombine sh rows c ell hd data)=
      payload data := CompactNativeRoleRecombine.rolePayload sh rows c ell hd data

/-- Retained role widths supply the whole-array Width required by the merger. -/
theorem width (sh : Shape) (rows ell p : ℕ) (hd : c ∣ rows) (hP : 2*sh.bits≤p)
    (data : Fin c → Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data j i).2.length=CompactNativeRoleHeaders.recordWidth sh p) :
    CompactSpectatorInheritedGrid.Width sh rows ell (p-2*sh.bits) (recombine sh rows c ell hd data) :=
  CompactSpectatorInheritedGrid.width_from_retained_role sh rows ell p hP _
    (CompactNativeRoleRecombine.width sh rows c ell _ hd data hw)

/-- The original whole-array grid comes directly from all corrected role grids. -/
theorem grid (sh : Shape) (rows ell q current M : ℕ) (hd : c ∣ rows)
    (data : Fin c → Array sh (rows/c) ell)
    (hg : ∀ j,CompactSpectatorInheritedGrid.Grid sh (rows/c) ell q current M (data j)) :
    CompactSpectatorInheritedGrid.Grid sh rows ell q current M (recombine sh rows c ell hd data) :=
  CompactNativeRoleRecombine.grid sh rows c ell q current M hd data hg

/-- Literal signed contraction commutes with the actual cyclic recombination. -/
theorem contracted_recombine (sh : Shape) (rows ell gap : ℕ) (hd : c ∣ rows)
    (data : Fin c → Array sh (rows/c) ell) :
    contracted gap (recombine sh rows c ell hd data)=
      recombine sh rows c ell hd (fun j => contracted gap (data j)) := rfl

/-- Coarser role-grid membership justifies exact contraction; the signed
capacity follows from the actual original Path and propagated live ledger. -/
theorem contracted_exact (sh : Shape) (rows ell p current target M : ℕ) (hd : c ∣ rows)
    (hP : 2*sh.bits≤p) (hle : target≤current)
    (data : Fin c → Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data j i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hg : ∀ j i,Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh (rows/c) ell (p-2*sh.bits) current (data j) i))
    {left k levels frames returned : ℕ} (path : Path sh.active left k levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    ∀ i,CompactSpectatorInheritedGrid.decoded sh rows ell (p-2*sh.bits) target
        (contracted (current-target) (recombine sh rows c ell hd data)) i=
      CompactSpectatorInheritedGrid.decoded sh rows ell (p-2*sh.bits) current
        (recombine sh rows c ell hd data) i := by
  have hcap := CompactComplexControllerExactReturnBudget.current_capacity path R base (p-2*sh.bits)
    usedRows current hb hu hroom hlive
  have hhalf := CompactComplexSourceReadyPrefixGeometry.retained_half (sh:=sh) p hP
  have hw' : ∀ i,(recombine sh rows c ell hd data i).1.length=
      CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 ∧
    (recombine sh rows c ell hd data i).2.length=
      CompactSpectatorInheritedGrid.half sh (p-2*sh.bits)+1 := by
    rw [hhalf]
    exact CompactNativeRoleRecombine.width sh rows c ell _ hd data hw
  have he := CompactComplexControllerExactReturn.contracted_exact
    (recombine sh rows c ell hd data) (CompactSpectatorInheritedGrid.half sh (p-2*sh.bits))
    current target M hle (by omega) hw' (fun _ => hg _ _)
  exact he.2

/-- Exact physical contraction produces the whole-array target grid. -/
theorem contracted_grid (sh : Shape) (rows ell p current target M : ℕ) (hd : c ∣ rows)
    (hP : 2*sh.bits≤p) (hle : target≤current)
    (data : Fin c → Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data j i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hg : ∀ j i,Networks.GaussianPrecision.BoundedGrid target M
      (CompactSpectatorInheritedGrid.decoded sh (rows/c) ell (p-2*sh.bits) current (data j) i))
    {left k levels frames returned : ℕ} (path : Path sh.active left k levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    CompactSpectatorInheritedGrid.Grid sh rows ell (p-2*sh.bits) target M
      (recombine sh rows c ell hd (fun j => contracted (current-target) (data j))) := by
  rw [←contracted_recombine]
  intro i
  rw [contracted_exact sh rows ell p current target M hd hP hle data hw hg path R base usedRows hb hu hroom hlive]
  exact hg _ _

/-- Actual all-role contraction and same-row merge, starting directly from the
completed family, with no assumed source whole array or role codec equality. -/
theorem raw_runs_native_linear (sh : Shape) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (data : Fin c → Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data j i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (data j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target (payload data))
    HoareTime (CompactComplexSourceReadyNonleafFinalPath.program (s:=s) (c:=c)).2
      (fun z => z=CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage (payload data)) (frame.append (SharedBank.empty 7 2)) leaf)
      (fun z => z=CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
        (recombine sh rows c ell hd (fun j => contracted (current-target) (data j))) (v.append frame) leaf)
      (CompactComplexSourceReadyNonleafFinalPath.constant c*volume rows sh ell p) := by
  have h := CompactComplexSourceReadyNonleafFinalPath.raw_runs_native_linear sh rows ell p
    hc hr hd hgroup hG hA hK hP rho left count slots right src dst control queue scalar tail storage (payload data)
    (recombine sh rows c ell hd data) (CompactNativeRoleRecombine.width sh rows c ell _ hd data hw)
    current target hle hcurrent htarget (payload_source data) (payload_roles sh rows ell hd data)
    path R base usedRows hb hu hroom frame leaf hlive
  simp_rw [CompactNativeRoleRecombine.role_recombine] at h
  rw [contracted_recombine] at h
  exact h

/-- The same root-capable final path retains arbitrary scalar scratch. -/
theorem full_raw_runs_native_linear (sh : Shape) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (data : Fin c → Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data j i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (data j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target (payload data))
    HoareTime (CompactComplexSourceReadyOrientedControls.widen
      (CompactComplexSourceReadyNonleafFinalPath.program (s:=s) (c:=c)).2)
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage (payload data)) (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=(CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
        (recombine sh rows c ell hd (fun j => contracted (current-target) (data j))) (v.append frame) leaf).append scratch)
      (CompactComplexSourceReadyNonleafFinalPath.constant c*volume rows sh ell p) :=
  CompactComplexSourceReadyOrientedControls.widen_runs
    (raw_runs_native_linear sh rows ell p hc hr hd hgroup hG hA hK hP rho left count slots right src dst
      control queue scalar tail storage data hw current target hle hcurrent htarget path R base usedRows
      hb hu hroom frame leaf hlive) scratch

/-- Complete oriented finalization from arbitrary corrected physical roles;
all saved-call, controller, ancestor and scalar workspace frames are retained. -/
theorem oriented_runs_native_linear (sh : Shape) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (data : Fin c → Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data j i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : FiniteReturnStack.bank (storage.tape (Fin.natAdd 10 pcStack)) (storage.head (Fin.natAdd 10 pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)))
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (data j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target (payload data))
    let joined := recombine sh rows c ell hd (fun j => contracted (current-target) (data j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
      joined (v.append frame) leaf
    HoareTime (CompactComplexSourceReadyNonleafOrientedFinal.program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage (payload data)) (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=(CompactComplexSourceReadyOrientation.output call w joined).append scratch)
      (CompactComplexSourceReadyNonleafOrientedFinal.constant c*volume rows sh ell p) := by
  have h := CompactComplexSourceReadyNonleafOrientedFinal.runs_native_linear sh rows ell p
    hc hr hd hgroup hG hA hK hP rho left count slots right src dst control queue scalar tail storage (payload data)
    (recombine sh rows c ell hd data) (CompactNativeRoleRecombine.width sh rows c ell _ hd data hw)
    current target hle hcurrent htarget (payload_source data) (payload_roles sh rows ell hd data)
    path R base usedRows hb hu hroom frame leaf pcStack call older origin hstack scratch hlive
  simp_rw [CompactNativeRoleRecombine.role_recombine] at h
  rw [contracted_recombine] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRoleRejoin
