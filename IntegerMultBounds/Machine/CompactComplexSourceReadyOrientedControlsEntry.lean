import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsFrame
import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedNodePath

/-! Actual pre-orientation followed by the original stopping guard reaches
its genuine finite marker, shifted through sequence and scalar widening. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsEntry
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexSourceReadyWorkspace (publicTapes tapes bank leafTapes)
open CompactComplexSourceReadyOrientationInvariants (savedSlot)
open CompactComplexSourceReadyOrientedControls (orientation entry nodeEntry isStopped)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyDirection.width
  CompactComplexSourceReadyGuard.setupProgram CompactComplexSourceReadyGuard.setupProgramFor
  CompactComplexSourceReadyGuard.setupCost CompactComplexSourceReadyGuard.cleanupCost
  CompactComplexSourceReadyGuard.guardConstant CompactComplexStopThreshold.base

private theorem sequence_widen_marker {t q r u : ℕ} (M : Program t q 2) (N : Program t r 2)
    (v : Tapes t 2) (mid : Config t q 2) (out : Config t r 2) (a b : ℕ)
    (har : run M a (v.start M)=some mid) (hah : step M mid=none)
    (hbr : run N b (mid.tapes.start N)=some out) (hbh : step N out=none)
    (scalar : Tapes u 2) (classify : Fin r → Bool) :
    ∃ final : Config (t+u) (q+r) 2,
      run (extend (seq M N) u) (a+1+b) ((v.append scalar).start (extend (seq M N) u))=some final ∧
      step (extend (seq M N) u) final=none ∧ final.tapes=out.tapes.append scalar ∧
      Fin.addCases (fun _ => false) classify final.state=classify out.state := by
  have hc := seq_run M N har hah hbr
  have hh := seq_halt_right M N hbh
  refine ⟨(out.mapState (Fin.natAdd q)).extend scalar,extend_run _ scalar hc,
    extend_halt _ scalar hh,rfl,?_⟩
  simp only [Config.extend,Config.mapState,Fin.addCases_right]

private theorem paid_cost (A G V a b S : ℕ) (ha : a≤A*V) (hb : b≤S)
    (hg : S≤G*V) (hv : 0<V) : a+1+b≤(A+G+1)*V := by
  nlinarith

private theorem guard_marker (v : Tapes (publicTapes s c) 2)
    (leaf : Tapes leafTapes 2) (work : Tapes 10 2) (D e : ℕ) (hD : 0<D)
    (h : CompactComplexSourceReadyGuard.Ready v)
    (hd : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head CompactComplexSourceReadyGuard.exponent=1 ∧
      v.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits e)) :
    ∃ n≤CompactComplexSourceReadyGuard.setupCost D e+CompactComplexSourceReadyGuard.cleanupCost D e+3,
      ∃ out : Config (tapes s c) (CompactComplexSourceReadyNodeControls.entry (s:=s) (c:=c)).1 2,
        run CompactComplexSourceReadyNodeControls.entry.2 n
          ((bank v leaf work).start CompactComplexSourceReadyNodeControls.entry.2)=some out ∧
        step CompactComplexSourceReadyNodeControls.entry.2 out=none ∧
        out.tapes=bank v leaf work ∧
        CompactComplexSourceReadyNodeControls.isStopped out.state=ComplexRecursiveCallSchema.stopped D e := by
  cases hs : ComplexRecursiveCallSchema.stopped D e
  · obtain ⟨n,hn,hr,hh,hc⟩ := CompactComplexSourceReadyNodeControls.entry_nonleaf v leaf work D e hD h hd he hs
    exact ⟨n,hn,_,hr,hh,rfl,hc⟩
  · obtain ⟨n,hn,hr,hh,hc⟩ := CompactComplexSourceReadyNodeControls.entry_stopped v leaf work D e hD h hd he hs
    exact ⟨n,hn,_,hr,hh,rfl,hc⟩

theorem runs_from_path {sh : Shape} {rows ell q left e levels frames returned : ℕ}
    (pcStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (v : Tapes (publicTapes s c) 2) (leaf : Tapes leafTapes 2) (work : Tapes 10 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (bank v leaf work)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (path : CompactRecursiveDependencyBudget.Path sh.active left e levels frames returned)
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
        CompactNativeRoleTransferBudget.volume rows sh ell (ButterflyIndependentGuardHeaders.reservation sh.bits q),
      ∃ out : Config (CompactComplexSourceReadyScalarWorkspace.tapes s c) (entry (c:=c) pcStack).1 2,
        run (entry pcStack).2 t (((bank v leaf work).append scalar).start (entry pcStack).2)=some out ∧
        step (entry pcStack).2 out=none ∧
        out.tapes=(bank (CompactComplexSourceReadyOrientedControlsFrame.output call v f) leaf work).append scalar ∧
        isStopped pcStack out.state=ComplexRecursiveCallSchema.stopped sh.axes e := by
  have ho := CompactComplexSourceReadyOrientationInvariants.runs_from_path pcStack call
    (bank v leaf work) older origin hstack path p C n hp hchunk hr f hw hg
    (by simpa only [CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
      CompactComplexSourceReadyOrientedControlsFrame.source,bank,Tapes.append,Fin.addCases_left] using hs)
    (by simpa only [CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
      CompactComplexSourceReadyOrientedControlsFrame.source,bank,Tapes.append,Fin.addCases_left] using hh)
  obtain ⟨a,mid,ha,har,hah,hpost⟩ := ho (bank v leaf work) rfl
  have hmid := hpost.1
  rw [CompactComplexSourceReadyOrientedControlsFrame.node_output] at hmid
  have hd' := hd
  have he' := he
  rw [←(CompactComplexSourceReadyOrientedControlsFrame.frame call v f _
    CompactComplexSourceReadyOrientedControlsFrame.dimension_ne).1,
    ←(CompactComplexSourceReadyOrientedControlsFrame.frame call v f _
    CompactComplexSourceReadyOrientedControlsFrame.dimension_ne).2] at hd'
  rw [←(CompactComplexSourceReadyOrientedControlsFrame.frame call v f _
    CompactComplexSourceReadyOrientedControlsFrame.exponent_ne).1,
    ←(CompactComplexSourceReadyOrientedControlsFrame.frame call v f _
    CompactComplexSourceReadyOrientedControlsFrame.exponent_ne).2] at he'
  obtain ⟨b,hb,out,hbr,hbh,hbt,hbc⟩ := guard_marker
    (CompactComplexSourceReadyOrientedControlsFrame.output call v f) leaf work sh.axes e hA
    (CompactComplexSourceReadyOrientedControlsFrame.ready call v f hready) hd' he'
  have hgRun : run CompactComplexSourceReadyNodeControls.entry.2 b
      (mid.tapes.start CompactComplexSourceReadyNodeControls.entry.2)=some out := by
    rw [hmid]
    exact hbr
  obtain ⟨final,hfr,hfh,hft,hfc⟩ := sequence_widen_marker (orientation (c:=c) pcStack)
    CompactComplexSourceReadyNodeControls.entry.2 (bank v leaf work) mid out a b har hah hgRun hbh
    scalar CompactComplexSourceReadyNodeControls.isStopped
  refine ⟨a+1+b,?_,final,hfr,hfh,?_,?_⟩
  · have hguard := CompactComplexSourceReadyStoppedNodePath.guard_cost_from_visit path.visit hactive
      rows ell (ButterflyIndependentGuardHeaders.reservation sh.bits q) hr hG
    have hv := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell
      (ButterflyIndependentGuardHeaders.reservation sh.bits q))
    change 0<CompactNativeRoleTransferBudget.volume rows sh ell
      (ButterflyIndependentGuardHeaders.reservation sh.bits q) at hv
    exact paid_cost _ _ _ _ _ _ ha hb hguard hv
  · exact hft.trans (congrArg (fun w => w.append scalar) hbt)
  · exact hfc.trans hbc

/-- Empty original root stacks select forward identity before the real guard. -/
theorem root_runs (pcStack : Fin s) (v : Tapes (publicTapes s c) 2)
    (leaf : Tapes leafTapes 2) (work : Tapes 10 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hstack : (bank v leaf work).tape (savedSlot pcStack)
      ((bank v leaf work).head (savedSlot pcStack)-1)=blank)
    (D e : ℕ) (hD : 0<D) (hready : CompactComplexSourceReadyGuard.Ready v)
    (hd : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head CompactComplexSourceReadyGuard.exponent=1 ∧
      v.tape CompactComplexSourceReadyGuard.exponent=RadixZeroFill.encodedBinary (bits e)) :
    ∃ t≤CompactComplexSourceReadyGuard.setupCost D e+CompactComplexSourceReadyGuard.cleanupCost D e+7,
      ∃ out : Config (CompactComplexSourceReadyScalarWorkspace.tapes s c) (entry (c:=c) pcStack).1 2,
        run (entry pcStack).2 t (((bank v leaf work).append scalar).start (entry pcStack).2)=some out ∧
        step (entry pcStack).2 out=none ∧ out.tapes=(bank v leaf work).append scalar ∧
        isStopped pcStack out.state=ComplexRecursiveCallSchema.stopped D e := by
  obtain ⟨a,mid,ha,har,hah,hmid⟩ :=
    CompactComplexSourceReadyOrientation.root_runs (savedSlot pcStack) (bank v leaf work) hstack
      (bank v leaf work) rfl
  obtain ⟨b,hb,out,hbr,hbh,hbt,hbc⟩ := guard_marker v leaf work D e hD hready hd he
  have hbr' : run CompactComplexSourceReadyNodeControls.entry.2 b
      (mid.tapes.start CompactComplexSourceReadyNodeControls.entry.2)=some out := by rw [hmid];exact hbr
  obtain ⟨final,hfr,hfh,hft,hfc⟩ := sequence_widen_marker (orientation (c:=c) pcStack)
    CompactComplexSourceReadyNodeControls.entry.2 (bank v leaf work) mid out a b har hah hbr' hbh
    scalar CompactComplexSourceReadyNodeControls.isStopped
  exact ⟨a+1+b,by omega,final,hfr,hfh,hft.trans (congrArg (fun w => w.append scalar) hbt),hfc.trans hbc⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsEntry
