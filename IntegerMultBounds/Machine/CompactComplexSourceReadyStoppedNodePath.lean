import IntegerMultBounds.Machine.CompactComplexSourceReadyNodeControls
import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatchBudget

/-! Actual stopped arithmetic reaches the real return guard in the cyclic
node table, preserving the source-ready endpoint and paying its table jump.
Both zero and positive exponents derive their block runtime from the Path. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedNodePath
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

open CompactComplexSourceReadyNodeControls (controls classify tableFamily tableNext)
open CompactComplexFixedNodeTable (controlPCFor controlEdgesWith)
open CompactComplexSourceReadyStoppedLeafDispatchBudget (constant)
variable {N length aw : ℕ}
attribute [local irreducible] CompactComplexSourceReadyGuard.guardConstant
  CompactComplexSourceReadyGuard.setupCost CompactComplexSourceReadyGuard.cleanupCost
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant
  CompactComplexStopThreshold.base

private def fixedSum (G C : ℕ) : ℕ :=
  Classical.choose (show ∃ n : ℕ,n=G+C+2 from ⟨G+C+2,rfl⟩)

private theorem fixedSum_eq (G C : ℕ) : fixedSum G C=G+C+2 :=
  Classical.choose_spec (show ∃ n : ℕ,n=G+C+2 from ⟨G+C+2,rfl⟩)

/-- An exact symbolic constant: the singleton choice prevents kernel reduction
of the astronomical fixed stopping base during later bound conversions. -/
def nodeConstant : ℕ := fixedSum (4*CompactComplexSourceReadyGuard.guardConstant) constant

theorem nodeConstant_eq : nodeConstant=4*CompactComplexSourceReadyGuard.guardConstant+constant+2 :=
  fixedSum_eq _ _

/-- Current-node geometry, including roots and scalar leaves, pays the actual
stopping test from native volume; a parent-only exponent bound is unnecessary. -/
theorem guard_cost_from_visit {sh : Shape} {left e : ℕ}
    (visit : Visit sh.active left e) (hactive : sh.active≤sh.axes)
    (rows ell p : ℕ) (hr : 0<rows) (hG : 0<sh.guard) :
    CompactComplexSourceReadyGuard.setupCost sh.axes e+
      CompactComplexSourceReadyGuard.cleanupCost sh.axes e+3≤
        (4*CompactComplexSourceReadyGuard.guardConstant)*volume rows sh ell p := by
  have he := Nat.lt_pow_self (n:=e) (by decide : 1<arity)
  have hf := visit.fits
  have hl := CompactComplexSourceReadyGuard.cost_linear sh.axes e
  have hs : sh.axes+e+1≤(sh.axes+1)^2 := by nlinarith only [he,hf,hactive]
  have hv := CompactComplexControllerChildBudget.dimension_square_le_volume (s:=sh) rows ell p hr (by omega)
  have hm := Nat.mul_le_mul_left CompactComplexSourceReadyGuard.guardConstant (hs.trans hv)
  exact hl.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm] using hm)

private theorem paid_path_cost (setup cleanup G C V M : ℕ)
    (hg : setup+cleanup+3≤G*V) (hv : 0<V) (hm : 0<M) :
    setup+cleanup+C*V*M+5≤(G+C+2)*V*M := by
  have hs := Nat.le_mul_of_pos_right (G*V) hm
  have hvn : 1≤V*M := Nat.succ_le_of_lt (Nat.mul_pos hv hm)
  have htwo := Nat.mul_le_mul_left 2 hvn
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

private theorem complete_cost {sh : Shape} {left e : ℕ}
    (visit : Visit sh.active left e) (hactive : sh.active≤sh.axes)
    (rows ell p : ℕ) (hr : 0<rows) (hG : 0<sh.guard) :
    CompactComplexSourceReadyGuard.setupCost sh.axes e+
      CompactComplexSourceReadyGuard.cleanupCost sh.axes e+constant*volume rows sh ell p*(arity^e)+5≤
        nodeConstant*volume rows sh ell p*(arity^e) := by
  rw [nodeConstant_eq]
  have hg := guard_cost_from_visit (sh:=sh) visit hactive rows ell p hr hG
  have hv : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hn : 0<arity^e := pow_pos (by decide) _
  exact paid_path_cost (CompactComplexSourceReadyGuard.setupCost sh.axes e)
    (CompactComplexSourceReadyGuard.cleanupCost sh.axes e)
    (4*CompactComplexSourceReadyGuard.guardConstant) constant
    (volume rows sh ell p) (arity^e) hg hv hn

private theorem stopped_local_path (dir : Direction) (hN : N≤2^aw)
    (stack : Fin (CompactComplexSourceReadyWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (before after : Tapes (CompactComplexSourceReadyWorkspace.tapes s c) 2) (B : ℕ)
    (h : HoareTime (CompactComplexSourceReadyStoppedLeafDispatch.program dir)
      (fun z => z=before) (fun z => z=after) B) :
    ∃ t≤B+1,FiniteFlowPath.Path (tableFamily (k:=aw) dir stack returns events)
      (tableNext dir hN returns events re ee) (controlPCFor N length 1) before t 0 after := by
  have hl : HoareTime (controls (s:=s) (c:=c) dir 1).2 (fun z => z=before) (fun z => z=after) B := h
  have he : ∀ st,controlEdgesWith (N:=N) (length:=length) (controls (s:=s) (c:=c) dir) (classify (s:=s) (c:=c) dir) 1 st=some 0 := by
    intro st
    rfl
  exact CompactComplexFixedNodePaths.control_local_path hN stack returns (controls (s:=s) (c:=c) dir) events re
    (controlEdgesWith (N:=N) (length:=length) (controls (s:=s) (c:=c) dir) (classify (s:=s) (c:=c) dir)) ee 1 0 before after B hl he

theorem positive_path (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    (hN : N≤2^aw) (stack : Fin (CompactComplexSourceReadyWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))

    {left k : ℕ} {levels frames returned : ℕ} (path : Path sh.active left (k+1) levels frames returned) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (k+1)))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames returned usedRows) :
    ∃ t≤constant*volume rows sh ell p*(arity^(k+1))+1,
      FiniteFlowPath.Path (tableFamily (k:=aw) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 1) (ready v) t 0
        (ready (CompactComplexSourceReadyStoppedLeafCount.returned v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n (k+1)))) := by
  have h := CompactComplexSourceReadyStoppedLeafDispatchBudget.positive_runs_linear dir sh rows ell p rho path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  exact stopped_local_path dir hN stack returns events re ee _ _ _ h

theorem scalar_path (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    (hN : N≤2^aw) (stack : Fin (CompactComplexSourceReadyWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))

    {left : ℕ} {levels frames returned : ℕ} (path : Path sh.active left 0 levels frames returned) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left 1 arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits 0))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames returned usedRows) :
    ∃ t≤constant*volume rows sh ell p*1+1,
      FiniteFlowPath.Path (tableFamily (k:=aw) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 1) (ready v) t 0
        (CompactComplexSourceReadyStoppedLeaf.output v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n 0)) := by
  have h := CompactComplexSourceReadyStoppedLeafDispatchBudget.scalar_runs_linear dir sh rows ell p rho path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  exact stopped_local_path dir hN stack returns events re ee _ _ _ h

theorem positive_entry_path (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    (hN : N≤2^aw) (stack : Fin (CompactComplexSourceReadyWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))

    {left k : ℕ} {levels frames returned : ℕ} (path : Path sh.active left (k+1) levels frames returned) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (k+1)))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames returned usedRows)
    (hguard : CompactComplexSourceReadyGuard.Ready v)
    (hdimension : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (hstopped : Networks.ComplexRecursiveCallSchema.stopped sh.axes (k+1)=true) :
    ∃ t≤CompactComplexSourceReadyGuard.setupCost sh.axes (k+1)+
      CompactComplexSourceReadyGuard.cleanupCost sh.axes (k+1)+constant*volume rows sh ell p*(arity^(k+1))+5,
      FiniteFlowPath.Path (tableFamily (k:=aw) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 0) (ready v) t 0
        (ready (CompactComplexSourceReadyStoppedLeafCount.returned v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n (k+1)))) := by
  have he : v.head CompactComplexSourceReadyGuard.exponent=1 ∧
      v.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits (k+1)) :=
    ⟨hexponentHead,hexponent⟩
  obtain ⟨t0,ht0,hp0⟩ := CompactComplexSourceReadyNodeControls.entry_stopped_path
    dir hN stack returns events re ee v (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)
      (SharedBank.empty 10 2) sh.axes (k+1) hA hguard hdimension he hstopped
  obtain ⟨t1,ht1,hp1⟩ := positive_path dir sh rows ell p rho hN stack returns events re ee path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  refine ⟨t0+t1,by omega,?_⟩
  exact FiniteFlowPath.append hp0 hp1

theorem scalar_entry_path (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    (hN : N≤2^aw) (stack : Fin (CompactComplexSourceReadyWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))

    {left : ℕ} {levels frames returned : ℕ} (path : Path sh.active left 0 levels frames returned) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left 1 arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits 0))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames returned usedRows)
    (hguard : CompactComplexSourceReadyGuard.Ready v)
    (hdimension : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (hstopped : Networks.ComplexRecursiveCallSchema.stopped sh.axes 0=true) :
    ∃ t≤CompactComplexSourceReadyGuard.setupCost sh.axes (0)+
      CompactComplexSourceReadyGuard.cleanupCost sh.axes (0)+constant*volume rows sh ell p*1+5,
      FiniteFlowPath.Path (tableFamily (k:=aw) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 0) (ready v) t 0
        (CompactComplexSourceReadyStoppedLeaf.output v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n 0)) := by
  have he : v.head CompactComplexSourceReadyGuard.exponent=1 ∧
      v.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits 0) :=
    ⟨hexponentHead,hexponent⟩
  obtain ⟨t0,ht0,hp0⟩ := CompactComplexSourceReadyNodeControls.entry_stopped_path
    dir hN stack returns events re ee v (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)
      (SharedBank.empty 10 2) sh.axes (0) hA hguard hdimension he hstopped
  obtain ⟨t1,ht1,hp1⟩ := scalar_path dir sh rows ell p rho hN stack returns events re ee path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  refine ⟨t0+t1,by omega,?_⟩
  exact FiniteFlowPath.append hp0 hp1


theorem positive_entry_path_linear (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    (hN : N≤2^aw) (stack : Fin (CompactComplexSourceReadyWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))

    {left k : ℕ} {levels frames returned : ℕ} (path : Path sh.active left (k+1) levels frames returned) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (k+1)))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames returned usedRows)
    (hguard : CompactComplexSourceReadyGuard.Ready v)
    (hdimension : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (hstopped : Networks.ComplexRecursiveCallSchema.stopped sh.axes (k+1)=true)
    (hactive : sh.active≤sh.axes) :
    ∃ t≤nodeConstant*volume rows sh ell p*(arity^(k+1)),
      FiniteFlowPath.Path (tableFamily (k:=aw) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 0) (ready v) t 0
        (ready (CompactComplexSourceReadyStoppedLeafCount.returned v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n (k+1)))) := by
  obtain ⟨t,ht,hpath⟩ := positive_entry_path dir sh rows ell p rho hN stack returns events re ee path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound hguard hdimension hstopped
  refine ⟨t,ht.trans ?_,hpath⟩
  exact complete_cost (sh:=sh) path.visit hactive rows ell p hr hG

theorem scalar_entry_path_linear (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    (hN : N≤2^aw) (stack : Fin (CompactComplexSourceReadyWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))

    {left : ℕ} {levels frames returned : ℕ} (path : Path sh.active left 0 levels frames returned) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left 1 arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits 0))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames returned usedRows)
    (hguard : CompactComplexSourceReadyGuard.Ready v)
    (hdimension : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (hstopped : Networks.ComplexRecursiveCallSchema.stopped sh.axes 0=true)
    (hactive : sh.active≤sh.axes) :
    ∃ t≤nodeConstant*volume rows sh ell p*1,
      FiniteFlowPath.Path (tableFamily (k:=aw) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 0) (ready v) t 0
        (CompactComplexSourceReadyStoppedLeaf.output v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n 0)) := by
  obtain ⟨t,ht,hpath⟩ := scalar_entry_path dir sh rows ell p rho hN stack returns events re ee path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound hguard hdimension hstopped
  refine ⟨t,ht.trans ?_,hpath⟩
  simpa only [pow_zero] using complete_cost (sh:=sh) path.visit hactive rows ell p hr hG


end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedNodePath
