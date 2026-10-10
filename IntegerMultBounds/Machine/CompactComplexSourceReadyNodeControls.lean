import IntegerMultBounds.Machine.CompactComplexSourceReadyWorkspace
import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatch
import IntegerMultBounds.Machine.CompactComplexFixedNodePaths
import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeCurrent

/-! Actual source-ready node control blocks. The entry's real stopping test
returns a finite-state marker after erasing all guard workspace. That marker
selects the stopped/nonleaf PCs of the existing fixed node table. Event and
return-address tables remain separate; this bank does not assert scalar room. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNodeControls
noncomputable section
open CompactComplexSourceReadyWorkspace (publicTapes tapes bank ready publicProgram)
open RecursiveChildQuotientsConstant (bits)
namespace Guard
export CompactComplexSourceReadyGuard (setupProgram cleanupProgram program leaf_ready recurse_ready
  Ready dimension exponent setupCost cleanupCost)
end Guard
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyGuard.setupProgram
  CompactComplexSourceReadyGuard.setupProgramFor

def marker : Program (publicTapes s c) 1 2 := skip _ _ (by
  change 0<CompactComplexNonleafRoleEntry.tapes (10+s) c+7
  omega)

def publicEntry : Σ q,Program (publicTapes s c) q 2 :=
  ⟨_,Guard.program (marker (s:=s) (c:=c)) marker⟩
def entry : Σ q,Program (tapes s c) q 2 := ⟨publicEntry.1,publicProgram publicEntry.2⟩

def stoppedState : Fin (entry (s:=s) (c:=c)).1 :=
  Fin.natAdd Guard.setupProgram.1 (leftState 16 16 (Fin.natAdd 15 (0 : Fin 1)))
def nonleafState : Fin (entry (s:=s) (c:=c)).1 :=
  Fin.natAdd Guard.setupProgram.1 (rightState 16 16 (Fin.natAdd 15 (0 : Fin 1)))
def isStopped (st : Fin (entry (s:=s) (c:=c)).1) : Bool := decide (st=stoppedState)

theorem classify_stopped : isStopped (stoppedState (s:=s) (c:=c))=true := by simp [isStopped]
theorem classify_nonleaf : isStopped (nonleafState (s:=s) (c:=c))=false := by
  simp only [isStopped,decide_eq_false_iff_not]
  intro h
  have hv := congrArg Fin.val h
  simp only [nonleafState,stoppedState,Fin.val_natAdd,rightState,leftState,Fin.val_castAdd] at hv
  omega

def stoppedConfig (v : Tapes (publicTapes s c) 2) : Config (publicTapes s c) (publicEntry (s:=s) (c:=c)).1 2 :=
  (((v.start marker).mapState (Fin.natAdd 15)).mapState (leftState 16 16)).mapState
    (Fin.natAdd Guard.setupProgram.1)
def nonleafConfig (v : Tapes (publicTapes s c) 2) : Config (publicTapes s c) (publicEntry (s:=s) (c:=c)).1 2 :=
  (((v.start marker).mapState (Fin.natAdd 15)).mapState (rightState 16 16)).mapState
    (Fin.natAdd Guard.setupProgram.1)

theorem stopped_halt (v : Tapes (publicTapes s c) 2) : step publicEntry.2 (stoppedConfig v)=none := by
  change step (seq Guard.setupProgram.2 (CompactComplexSourceReadyGuard.dispatch marker marker))
    ((((v.start marker).mapState (Fin.natAdd 15)).mapState (leftState 16 16)).mapState
      (Fin.natAdd Guard.setupProgram.1))=none
  rw [seq_step_right]
  unfold CompactComplexSourceReadyGuard.dispatch
  rw [branch_step_left,seq_step_right]
  rfl

theorem nonleaf_halt (v : Tapes (publicTapes s c) 2) : step publicEntry.2 (nonleafConfig v)=none := by
  change step (seq Guard.setupProgram.2 (CompactComplexSourceReadyGuard.dispatch marker marker))
    ((((v.start marker).mapState (Fin.natAdd 15)).mapState (rightState 16 16)).mapState
      (Fin.natAdd Guard.setupProgram.1))=none
  rw [seq_step_right]
  unfold CompactComplexSourceReadyGuard.dispatch
  rw [branch_step_right,seq_step_right]
  rfl

/-- The actual entry executes on the common bank and reaches its stopped
marker with every input tape/head restored and both common suffixes retained. -/
theorem entry_stopped (v : Tapes (publicTapes s c) 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (D e : ℕ) (hD : 0<D) (h : Guard.Ready v)
    (hd : v.head Guard.dimension=1 ∧ v.tape Guard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head Guard.exponent=1 ∧ v.tape Guard.exponent=RadixZeroFill.encodedBinary (bits e))
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=true) :
    ∃ n≤Guard.setupCost D e+Guard.cleanupCost D e+3,
      run entry.2 n ((bank v leaf work).start entry.2)=some (((stoppedConfig v).extend leaf).extend work) ∧
      step entry.2 (((stoppedConfig v).extend leaf).extend work)=none ∧
      isStopped (((stoppedConfig v).extend leaf).extend work).state=true := by
  obtain ⟨n,hn,hr⟩ := Guard.leaf_ready marker marker v D e hD h hd he hs
  refine ⟨n,hn,?_,?_,classify_stopped⟩
  · exact CompactComplexSourceReadyWorkspace.public_run publicEntry.2 leaf work hr
  · exact extend_halt _ work (extend_halt _ leaf (stopped_halt v))

theorem entry_nonleaf (v : Tapes (publicTapes s c) 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (D e : ℕ) (hD : 0<D) (h : Guard.Ready v)
    (hd : v.head Guard.dimension=1 ∧ v.tape Guard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head Guard.exponent=1 ∧ v.tape Guard.exponent=RadixZeroFill.encodedBinary (bits e))
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=false) :
    ∃ n≤Guard.setupCost D e+Guard.cleanupCost D e+3,
      run entry.2 n ((bank v leaf work).start entry.2)=some (((nonleafConfig v).extend leaf).extend work) ∧
      step entry.2 (((nonleafConfig v).extend leaf).extend work)=none ∧
      isStopped (((nonleafConfig v).extend leaf).extend work).state=false := by
  obtain ⟨n,hn,hr⟩ := Guard.recurse_ready marker marker v D e hD h hd he hs
  refine ⟨n,hn,?_,?_,classify_nonleaf⟩
  · exact CompactComplexSourceReadyWorkspace.public_run publicEntry.2 leaf work hr
  · exact extend_halt _ work (extend_halt _ leaf (nonleaf_halt v))

/-- Controls contain actual fixed subroutines, rather than a supplied guard
callback. The stopped adapter's positive-node geometry contract is separate. -/
def controls (dir : CompactSpectatorLeafGuardOriginal.Direction) : Fin 4 → Σ q,Program (tapes s c) q 2 :=
  ![entry,
    ⟨_,CompactComplexSourceReadyStoppedLeafDispatch.program (s:=s) (c:=c) dir⟩,
    ⟨_,publicProgram (CompactComplexNonleafRolePreparation.splitCurrentProgram s c)⟩,
    ⟨_,publicProgram (CompactComplexNonleafRoleMergeCurrent.program (10+s) c)⟩]

theorem controls_entry (dir : CompactSpectatorLeafGuardOriginal.Direction) :
    controls (s:=s) (c:=c) dir 0=entry := rfl

def classify (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (st : Fin (controls (s:=s) (c:=c) dir 0).1) := isStopped st

/-- The actual stopped marker points to the shared stopped PC in the genuine
four-control successor table, after all cleanup has physically finished. -/
theorem stopped_edge (dir : CompactSpectatorLeafGuardOriginal.Direction) (N length : ℕ) :
    CompactComplexFixedNodeTable.controlEdgesWith (N:=N) (length:=length)
      (controls (s:=s) (c:=c) dir) (classify dir) 0 stoppedState=
      some (CompactComplexFixedNodeTable.controlPCFor N length 1) := by
  simp [CompactComplexFixedNodeTable.controlEdgesWith,classify,classify_stopped]

theorem nonleaf_edge (dir : CompactSpectatorLeafGuardOriginal.Direction) (N length : ℕ) :
    CompactComplexFixedNodeTable.controlEdgesWith (N:=N) (length:=length)
      (controls (s:=s) (c:=c) dir) (classify dir) 0 nonleafState=
      some (CompactComplexFixedNodeTable.controlPCFor N length 2) := by
  simp [CompactComplexFixedNodeTable.controlEdgesWith,classify,classify_nonleaf]


section Table
open CompactComplexFixedNodeTable
variable {N length k : ℕ}

def tablePrograms (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2) :=
  tableProgramsWith returns (controls dir) events

def tableFamily (dir : CompactSpectatorLeafGuardOriginal.Direction) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2) :=
  GuardedFiniteReturnExtraFlow.family (k:=k) stack
    (fun pc => (tablePrograms dir returns events pc).1)
    (fun pc => (tablePrograms dir returns events pc).2)

def tableNext (dir : CompactSpectatorLeafGuardOriginal.Direction) (hN : N≤2^k)
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2))) :=
  GuardedFiniteReturnExtraFlow.next hN
    (fun pc => (tablePrograms dir returns events pc).1)
    (tableEdgesWith returns (controls dir) events re
      (controlEdgesWith (N:=N) (length:=length) (controls dir) (classify dir)) ee)

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

/-- Reachability uses the actual terminal state of the executed stopping test;
no uniform successor contract on invalid entry states is imposed. -/
theorem entry_marker_path (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (hN : N≤2^k) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (before : Tapes (tapes s c) 2) (n : ℕ) (out : Config (tapes s c) entry.1 2)
    (hr : run entry.2 n (before.start entry.2)=some out)
    (hh : step entry.2 out=none) (outcome : Bool) (hc : isStopped out.state=outcome) :
    FiniteFlowPath.Path (tableFamily (k:=k) dir stack returns events)
      (tableNext dir hN returns events re ee) (controlPCFor N length 0) before (n+1)
      (controlPCFor N length (if outcome then 1 else 2)) out.tapes := by
  let pc : Fin (N+(4+length)) := Fin.natAdd N (Fin.castAdd length (0 : Fin 4))
  have hprogram : (⟨GuardedFiniteReturnExtraFlow.states (k:=k)
      (fun pc => (tablePrograms dir returns events pc).1) pc.succ.succ,
      tableFamily (k:=k) dir stack returns events pc.succ.succ⟩ : Σ q,Program (tapes s c) q 2)=entry := by
    rw [tableFamily,family_block]
    change tablePrograms dir returns events pc=entry
    simp only [tablePrograms,tableProgramsWith,pc,Fin.addCases_right,Fin.addCases_left,controls_entry]
  let out' := out.mapState (Fin.cast (congrArg Sigma.fst hprogram).symm)
  have hr' := sigma_run hprogram before n out hr
  have hh' := sigma_halt hprogram out hh
  have hnext : (⟨GuardedFiniteReturnExtraFlow.states (k:=k)
      (fun pc => (tablePrograms dir returns events pc).1) pc.succ.succ,
      tableNext dir hN returns events re ee pc.succ.succ⟩ :
        Σ q,Fin q → Option (Fin (N+(4+length)+2)))=
      ⟨(entry (s:=s) (c:=c)).1,fun st =>
        some (if isStopped st then controlPCFor N length 1 else controlPCFor N length 2)⟩ := by
    exact (next_block hN (fun pc => (tableProgramsWith returns (controls dir) events pc).1)
      (tableEdgesWith returns (controls dir) events re
        (controlEdgesWith (N:=N) (length:=length) (controls dir) (classify dir)) ee) pc).trans
      (edge_control_block returns (controls dir) events re
        (controlEdgesWith (N:=N) (length:=length) (controls dir) (classify dir)) ee 0)
  have he : tableNext dir hN returns events re ee pc.succ.succ out'.state=
      some (controlPCFor N length (if outcome then 1 else 2)) := by
    have hh := sigma_apply hnext out.state
    change tableNext dir hN returns events re ee pc.succ.succ out'.state=
      some (if isStopped out.state then controlPCFor N length 1 else controlPCFor N length 2) at hh
    rw [hc] at hh
    cases outcome <;> exact hh
  exact FiniteFlowPath.block_path (family:=tableFamily (k:=k) dir stack returns events)
    (next:=tableNext dir hN returns events re ee) pc.succ.succ _ before n out' hr' hh' he

/-- Actual common-bank entry plus the real cyclic-table jump reaches the
shared stopped continuation, charging the jump and restoring every input tape. -/
theorem entry_stopped_path (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (hN : N≤2^k) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (v : Tapes (publicTapes s c) 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (D e : ℕ) (hD : 0<D) (h : Guard.Ready v)
    (hd : v.head Guard.dimension=1 ∧ v.tape Guard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head Guard.exponent=1 ∧ v.tape Guard.exponent=RadixZeroFill.encodedBinary (bits e))
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=true) :
    ∃ n≤Guard.setupCost D e+Guard.cleanupCost D e+4,
      FiniteFlowPath.Path (tableFamily (k:=k) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 0) (bank v leaf work) n
        (controlPCFor N length 1) (bank v leaf work) := by
  obtain ⟨n,hn,hr,hh,hc⟩ := entry_stopped v leaf work D e hD h hd he hs
  refine ⟨n+1,by omega,?_⟩
  exact entry_marker_path dir hN stack returns events re ee (bank v leaf work) n
    (((stoppedConfig v).extend leaf).extend work) hr hh true hc

/-- Actual common-bank entry plus the real cyclic-table jump reaches the
shared nonleaf continuation, charging the jump and restoring every input tape. -/
theorem entry_nonleaf_path (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (hN : N≤2^k) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (v : Tapes (publicTapes s c) 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (D e : ℕ) (hD : 0<D) (h : Guard.Ready v)
    (hd : v.head Guard.dimension=1 ∧ v.tape Guard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head Guard.exponent=1 ∧ v.tape Guard.exponent=RadixZeroFill.encodedBinary (bits e))
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=false) :
    ∃ n≤Guard.setupCost D e+Guard.cleanupCost D e+4,
      FiniteFlowPath.Path (tableFamily (k:=k) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 0) (bank v leaf work) n
        (controlPCFor N length 2) (bank v leaf work) := by
  obtain ⟨n,hn,hr,hh,hc⟩ := entry_nonleaf v leaf work D e hD h hd he hs
  refine ⟨n+1,by omega,?_⟩
  exact entry_marker_path dir hN stack returns events re ee (bank v leaf work) n
    (((nonleafConfig v).extend leaf).extend work) hr hh false hc


/-- The local node paths are literal runs of the existing fixed cyclic table,
including its guard/pop blocks and original return-address family. -/
theorem path_run (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (hN : N≤2^k) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    {pc last : Fin (N+(4+length)+2)} {before after : Tapes (tapes s c) 2} {n : ℕ}
    (hp : FiniteFlowPath.Path (tableFamily (k:=k) dir stack returns events)
      (tableNext dir hN returns events re ee) pc before n last after) :
    run (fixedProgramWith hN stack returns (controls dir) events re (classify dir) ee) n
      ((before.start (tableFamily (k:=k) dir stack returns events pc)).mapState
        (FiniteFlow.embed _ pc))=
      some ((after.start (tableFamily (k:=k) dir stack returns events last)).mapState
        (FiniteFlow.embed _ last)) :=
  FiniteFlowPath.path_run (controlPCFor N length 0) hp

end Table

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNodeControls
