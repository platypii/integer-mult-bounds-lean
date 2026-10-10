import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedSavedReturnPath

/-! The real pre-orientation and stopping classifier enter tag1 or tag2 of
the actual corrected cyclic table. Both child and empty-root paths retain all
private suffixes and pay the physical join, without an execution callback. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedClassifierTablePath
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexSourceReadyWorkspace (publicTapes bank leafTapes)
open CompactComplexSourceReadyOrientationInvariants (savedSlot)
open CompactComplexSourceReadyOrientedControls (entry isStopped)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexSourceReadyCorrectedActualTable (controls classify savedStackSlot)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexFixedNodeTable
open CompactComplexSourceReadyCorrectedSavedReturnPath (positive path)
variable {s : ℕ}
local notation "RC" => CompactComplexSourceReadyScalarWorkspace.roles
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyDirection.width
  CompactComplexCallReturn.addressWidth CompactComplexCallReturn.addressCount
  returnDestination eventDestination

namespace Marker
private theorem endpoint {α : Type*} (P : α → Prop) {a b : α}
    (ha : P a) (h : a=b) : P b := h ▸ ha

private theorem family_block {t a N extra k : ℕ} (stack : Fin t)
    (rest : Fin (N+extra) → ℕ) (blocks : ∀ pc,Program t (rest pc) a) (pc : Fin (N+extra)) :
    (⟨GuardedFiniteReturnExtraFlow.states (k:=k) rest pc.succ.succ,
      GuardedFiniteReturnExtraFlow.family (k:=k) stack rest blocks pc.succ.succ⟩ : Σ q,Program t q a)=
      ⟨rest pc,blocks pc⟩ := by
  simp [GuardedFiniteReturnExtraFlow.family,GuardedFiniteReturnExtraFlow.states,
    Fin.cases,Fin.induction,Fin.induction.go]

private theorem sigma_run {t a : ℕ} {P Q : Σ q,Program t q a} (h : P=Q)
    (before : Tapes t a) (n : ℕ) (out : Config t Q.1 a)
    (hr : run Q.2 n (before.start Q.2)=some out) :
    run P.2 n (before.start P.2)=some (out.mapState (Fin.cast (congrArg Sigma.fst h).symm)) := by
  cases h
  simpa only [Fin.cast_refl,Config.mapState,id_eq] using hr

private theorem sigma_halt {t a : ℕ} {P Q : Σ q,Program t q a} (h : P=Q)
    (out : Config t Q.1 a) (hh : step Q.2 out=none) :
    step P.2 (out.mapState (Fin.cast (congrArg Sigma.fst h).symm))=none := by
  cases h
  simpa only [Fin.cast_refl,Config.mapState,id_eq] using hh

private theorem next_block {N extra k : ℕ} (hN : N≤2^k)
    (rest : Fin (N+extra) → ℕ)
    (edges : ∀ pc,Fin (rest pc) → Option (Fin (N+extra+2))) (pc : Fin (N+extra)) :
    (⟨GuardedFiniteReturnExtraFlow.states (k:=k) rest pc.succ.succ,
      GuardedFiniteReturnExtraFlow.next hN rest edges pc.succ.succ⟩ :
        Σ q,Fin q → Option (Fin (N+extra+2)))=⟨rest pc,edges pc⟩ := by
  simp [GuardedFiniteReturnExtraFlow.next,GuardedFiniteReturnExtraFlow.states,
    Fin.cases,Fin.induction,Fin.induction.go]

private theorem sigma_apply {n : ℕ}
    {P Q : Σ q,Fin q → Option (Fin n)} (h : P=Q) (st : Fin Q.1) :
    P.2 (Fin.cast (congrArg Sigma.fst h).symm st)=Q.2 st := by
  cases h
  rfl

private theorem sigma_mpr {a b n : ℕ}
    (h : (Fin a → Option (Fin n))=(Fin b → Option (Fin n))) (hq : a=b)
    (f : Fin b → Option (Fin n)) :
    (⟨a,Eq.mpr h f⟩ : Σ q,Fin q → Option (Fin n))=⟨b,f⟩ := by
  subst b
  have hh : h=rfl := Subsingleton.elim _ _
  cases hh
  rfl

private theorem edge_control_block {t N length : ℕ}
    (returns : Fin N → Σ q,Program t q 2)
    (ctrl : Fin 4 → Σ q,Program t q 2) (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ce : ∀ pc,Fin (ctrl pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2))) (tag : Fin 4) :
    (⟨(tableProgramsWith returns ctrl events (Fin.natAdd N (Fin.castAdd length tag))).1,
      tableEdgesWith returns ctrl events re ce ee (Fin.natAdd N (Fin.castAdd length tag))⟩ :
        Σ q,Fin q → Option (Fin (N+(4+length)+2)))=⟨(ctrl tag).1,ce tag⟩ := by
  simp only [tableEdgesWith,Fin.addCases_right,Fin.addCases_left]
  generalize_proofs h
  exact sigma_mpr h (by simp only [tableProgramsWith,Fin.addCases_right,Fin.addCases_left]) _


private theorem halted_path {t N length k : ℕ} (hN : N≤2^k) (stack : Fin t)
    (returns : Fin N → Σ q,Program t q 2) (ctrl : Fin 4 → Σ q,Program t q 2)
    (events : Fin length → Σ q,Program t q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (classifier : Fin (ctrl 0).1 → Bool) (before : Tapes t 2) (n : ℕ)
    (out : Config t (ctrl 0).1 2) (hr : run (ctrl 0).2 n (before.start (ctrl 0).2)=some out)
    (hh : step (ctrl 0).2 out=none) (outcome : Bool) (hc : classifier out.state=outcome) :
    FiniteFlowPath.Path
      (GuardedFiniteReturnExtraFlow.family (k:=k) stack
        (fun pc => (tableProgramsWith returns ctrl events pc).1)
        (fun pc => (tableProgramsWith returns ctrl events pc).2))
      (GuardedFiniteReturnExtraFlow.next hN
        (fun pc => (tableProgramsWith returns ctrl events pc).1)
        (tableEdgesWith returns ctrl events re (controlEdgesWith ctrl classifier) ee))
      (controlPCFor N length 0) before (n+1)
      (controlPCFor N length (if outcome then 1 else 2)) out.tapes := by
  let pc : Fin (N+(4+length)) := Fin.natAdd N (Fin.castAdd length (0 : Fin 4))
  let programs := tableProgramsWith returns ctrl events
  let states := fun pc => (programs pc).1
  let blocks := fun pc => (programs pc).2
  let edges := tableEdgesWith returns ctrl events re (controlEdgesWith ctrl classifier) ee
  let family := GuardedFiniteReturnExtraFlow.family (k:=k) stack states blocks
  let next := GuardedFiniteReturnExtraFlow.next hN states edges
  have hprogram : (⟨GuardedFiniteReturnExtraFlow.states (k:=k) states pc.succ.succ,
      family pc.succ.succ⟩ : Σ q,Program t q 2)=ctrl 0 := by
    rw [show (⟨GuardedFiniteReturnExtraFlow.states (k:=k) states pc.succ.succ,
      family pc.succ.succ⟩ : Σ q,Program t q 2)=⟨states pc,blocks pc⟩ from family_block stack states blocks pc]
    change tableProgramsWith returns ctrl events pc=ctrl 0
    simp only [tableProgramsWith,pc,Fin.addCases_right,Fin.addCases_left]
  let out' := out.mapState (Fin.cast (congrArg Sigma.fst hprogram).symm)
  have hr' := sigma_run hprogram before n out hr
  have hh' := sigma_halt hprogram out hh
  have hnext : (⟨GuardedFiniteReturnExtraFlow.states (k:=k) states pc.succ.succ,
      next pc.succ.succ⟩ : Σ q,Fin q → Option (Fin (N+(4+length)+2)))=
      ⟨(ctrl 0).1,fun st => some (if classifier st then controlPCFor N length 1 else controlPCFor N length 2)⟩ := by
    exact (next_block hN states edges pc).trans
      (edge_control_block returns ctrl events re (controlEdgesWith ctrl classifier) ee 0)
  have he : next pc.succ.succ out'.state=some (controlPCFor N length (if outcome then 1 else 2)) := by
    have hd := sigma_apply hnext out.state
    change next pc.succ.succ out'.state=some
      (if classifier out.state then controlPCFor N length 1 else controlPCFor N length 2) at hd
    rw [hc] at hd
    cases outcome <;> exact hd
  exact FiniteFlowPath.block_path (family:=family) (next:=next) pc.succ.succ _ before n out' hr' hh' he
private theorem canonical_path {t : ℕ} (ht : 0<t) (stack : Fin t)
    (ret : ComplexRecursiveCallSchema.Call → Σ q,Program t q 2)
    (ctrl : Fin 4 → Σ q,Program t q 2)
    (events : CompactComplexCompletedLiveLower.Event → Σ q,Program t q 2)
    (classifier : Fin (ctrl 0).1 → Bool) (before : Tapes t 2) (n : ℕ)
    (out : Config t (ctrl 0).1 2)
    (hr : run (ctrl 0).2 n (before.start (ctrl 0).2)=some out)
    (hh : step (ctrl 0).2 out=none) (outcome : Bool) (hc : classifier out.state=outcome) :
    CompactComplexFixedNodePaths.nodePath ht stack ret ctrl events classifier
      (controlPCFor originalCount schedule.length 0) before (n+1)
      (controlPCFor originalCount schedule.length (if outcome then 1 else 2)) out.tapes := by
  exact halted_path (N:=originalCount) (length:=schedule.length)
    (CompactComplexCallReturn.roomFor ComplexRecursiveCallSchema.sites.length (25^3)) stack
    (returnPrograms ht ret) ctrl (fun i => events (schedule.get i))
    (fun address _ => returnDestination address) (fun i _ => eventDestination i)
    classifier before n out hr hh outcome hc
end Marker

theorem child_path {sh : Shape} {rows ell q left e levels frames returned : ℕ}
    (headerStack pcStack liveStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (publicTapes s RC) 2) (leaf : Tapes leafTapes 2) (work : Tapes 10 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (bank v leaf work)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (dependency : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned)
    (p C n : ℕ) (hp : p≤q) (hchunk : CompactSpectatorInheritedGrid.dependencyCoefficient C≤sh.chunk)
    (hr : 0<rows) (hG : 0<sh.guard) (hA : 0<sh.axes) (hactive : sh.active≤sh.axes)
    (f : Array sh rows ell) (hw : CompactSpectatorInheritedGrid.Width sh rows ell q f)
    (hg : CompactSpectatorInheritedGrid.Grid sh rows ell q n
      (CompactRecursiveGridBudget.bound p C levels (frames+2*returned)) f)
    (hs : v.tape CompactComplexSourceReadyOrientedControlsFrame.source=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f))
    (hh : v.head CompactComplexSourceReadyOrientedControlsFrame.source=0)
    (hready : CompactComplexSourceReadyGuard.Ready v)
    (hd : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (he : v.head CompactComplexSourceReadyGuard.exponent=1 ∧
      v.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits e)) :
    ∃ t≤(CompactComplexSourceReadyOrientationInvariants.constant+
        4*CompactComplexSourceReadyGuard.guardConstant+1)*
        CompactNativeRoleTransferBudget.volume rows sh ell (ButterflyIndependentGuardHeaders.reservation sh.bits q)+1,path headerStack pcStack liveStack
      (controlPCFor originalCount schedule.length 0) ((bank v leaf work).append scalar) t
      (controlPCFor originalCount schedule.length (if ComplexRecursiveCallSchema.stopped sh.axes e then 1 else 2)) ((bank (CompactComplexSourceReadyOrientedControlsFrame.output call v f) leaf work).append scalar) := by
  obtain ⟨t,ht,out,hrun,hhalt,hpost,hclass⟩ := CompactComplexSourceReadyOrientedControlsEntry.runs_from_path
    pcStack call v leaf work scalar older origin hstack dependency p C n hp hchunk hr hG hA hactive f hw hg hs hh hready hd he
  have hp := Marker.canonical_path (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack)
    (controls pcStack) (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)
    ((bank v leaf work).append scalar) t out hrun hhalt (ComplexRecursiveCallSchema.stopped sh.axes e) hclass
  change path headerStack pcStack liveStack (controlPCFor originalCount schedule.length 0)
    ((bank v leaf work).append scalar) (t+1) (controlPCFor originalCount schedule.length (if ComplexRecursiveCallSchema.stopped sh.axes e then 1 else 2)) out.tapes at hp
  exact ⟨t+1,Nat.add_le_add_right ht 1,Marker.endpoint _ hp hpost⟩


theorem root_path (headerStack pcStack liveStack : Fin s) (v : Tapes (publicTapes s RC) 2)
    (leaf : Tapes leafTapes 2) (work : Tapes 10 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hstack : (bank v leaf work).tape (savedSlot pcStack)
      ((bank v leaf work).head (savedSlot pcStack)-1)=blank)
    (D e : ℕ) (hD : 0<D) (hready : CompactComplexSourceReadyGuard.Ready v)
    (hd : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head CompactComplexSourceReadyGuard.exponent=1 ∧
      v.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits e)) :
    ∃ t≤CompactComplexSourceReadyGuard.setupCost D e+CompactComplexSourceReadyGuard.cleanupCost D e+7+1,path headerStack pcStack liveStack
      (controlPCFor originalCount schedule.length 0) ((bank v leaf work).append scalar) t
      (controlPCFor originalCount schedule.length (if ComplexRecursiveCallSchema.stopped D e then 1 else 2)) ((bank v leaf work).append scalar) := by
  obtain ⟨t,ht,out,hrun,hhalt,hpost,hclass⟩ := CompactComplexSourceReadyOrientedControlsEntry.root_runs
    pcStack v leaf work scalar hstack D e hD hready hd he
  have hp := Marker.canonical_path (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack)
    (controls pcStack) (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)
    ((bank v leaf work).append scalar) t out hrun hhalt (ComplexRecursiveCallSchema.stopped D e) hclass
  change path headerStack pcStack liveStack (controlPCFor originalCount schedule.length 0)
    ((bank v leaf work).append scalar) (t+1) (controlPCFor originalCount schedule.length (if ComplexRecursiveCallSchema.stopped D e then 1 else 2)) out.tapes at hp
  exact ⟨t+1,Nat.add_le_add_right ht 1,Marker.endpoint _ hp hpost⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedClassifierTablePath
