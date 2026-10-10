import IntegerMultBounds.Machine.CompactComplexSourceReadyNodeControls
import IntegerMultBounds.Machine.CompactComplexSourceReadyScalarWorkspace
import IntegerMultBounds.Machine.FiniteFlowFrames

/-! Actual source-ready node controls on the complete fixed scalar workspace.
Return and scalar event blocks may use the full bank; the physical entry,
stopped leaf, split and merge preserve its arbitrary added suffix. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyFullNodeControls
noncomputable section
open CompactComplexSourceReadyScalarWorkspace (tapes nodeTapes scratch)
open CompactComplexSourceReadyWorkspace (publicTapes bank)
open RecursiveChildQuotientsConstant (bits)
namespace Guard
export CompactComplexSourceReadyNodeControls.Guard (Ready dimension exponent setupCost cleanupCost)
end Guard
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyGuard.setupProgram
  CompactComplexSourceReadyGuard.setupProgramFor

def lift (P : Σ q,Program (nodeTapes s c) q 2) : Σ q,Program (tapes s c) q 2 :=
  ⟨P.1,extend P.2 scratch⟩

def entry : Σ q,Program (tapes s c) q 2 := lift CompactComplexSourceReadyNodeControls.entry

def controls (dir : CompactSpectatorLeafGuardOriginal.Direction) :
    Fin 4 → Σ q,Program (tapes s c) q 2 :=
  fun i => lift (CompactComplexSourceReadyNodeControls.controls dir i)

theorem controls_entry (dir : CompactSpectatorLeafGuardOriginal.Direction) :
    controls (s:=s) (c:=c) dir 0=entry := rfl

def isStopped (st : Fin (entry (s:=s) (c:=c)).1) : Bool :=
  CompactComplexSourceReadyNodeControls.isStopped st

def classify (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (st : Fin (controls (s:=s) (c:=c) dir 0).1) := isStopped st

/-- Exact runtime and complete endpoint lift for any existing actual child
entry or decoded-return block; the added scalar bank may be nonblank. -/
theorem lift_runs (P : Σ q,Program (nodeTapes s c) q 2)
    (before after : Tapes (nodeTapes s c) 2) (extra : Tapes scratch 2) (B : ℕ)
    (h : HoareTime P.2 (fun v => v=before) (fun v => v=after) B) :
    HoareTime (lift P).2 (fun v => v=before.append extra)
      (fun v => v=after.append extra) B := hoare_extend_eq h extra

/-- Every control is its genuine existing tape algorithm, retaining arbitrary
scalar scratch and exactly the original transition count. -/
theorem control_runs (dir : CompactSpectatorLeafGuardOriginal.Direction) (tag : Fin 4)
    (before after : Tapes (nodeTapes s c) 2) (extra : Tapes scratch 2) (B : ℕ)
    (h : HoareTime (CompactComplexSourceReadyNodeControls.controls dir tag).2
      (fun v => v=before) (fun v => v=after) B) :
    HoareTime (controls dir tag).2 (fun v => v=before.append extra)
      (fun v => v=after.append extra) B := hoare_extend_eq h extra

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

/-- Exact identity of each widened control block in the actual full table;
no scalar event or return block is forced to reuse an old state cardinality. -/
theorem table_control_program (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2) (tag : Fin 4) :
    (⟨GuardedFiniteReturnExtraFlow.states (k:=k)
      (fun pc => (tablePrograms dir returns events pc).1) (controlPCFor N length tag),
      tableFamily (k:=k) dir stack returns events (controlPCFor N length tag)⟩ :
      Σ q,Program (tapes s c) q 2)=controls dir tag := by
  rw [tableFamily]
  change (⟨_,GuardedFiniteReturnExtraFlow.family (k:=k) stack
    (fun pc => (tablePrograms dir returns events pc).1)
    (fun pc => (tablePrograms dir returns events pc).2)
    (Fin.natAdd N (Fin.castAdd length tag)).succ.succ⟩ : Σ q,Program (tapes s c) q 2)=controls dir tag
  rw [family_block]
  change tablePrograms dir returns events (Fin.natAdd N (Fin.castAdd length tag))=controls dir tag
  simp only [tablePrograms,tableProgramsWith,Fin.addCases_right,Fin.addCases_left]

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


/-- Existing actual local control executions install directly in the full
fixed table, preserving the scalar suffix and charging the genuine edge. -/
theorem control_path (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (hN : N≤2^k) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (tag : Fin 4) (dest : Fin (N+(4+length)+2))
    (before after : Tapes (nodeTapes s c) 2) (extra : Tapes scratch 2) (B : ℕ)
    (h : HoareTime (CompactComplexSourceReadyNodeControls.controls dir tag).2
      (fun v => v=before) (fun v => v=after) B)
    (hedge : ∀ st,controlEdgesWith (N:=N) (length:=length) (controls (s:=s) (c:=c) dir)
      (classify dir) tag st=some dest) :
    ∃ n≤B+1,FiniteFlowPath.Path (tableFamily (k:=k) dir stack returns events)
      (tableNext dir hN returns events re ee) (controlPCFor N length tag)
      (before.append extra) n dest (after.append extra) :=
  CompactComplexFixedNodePaths.control_local_path hN stack returns (controls dir) events re
    (controlEdgesWith (N:=N) (length:=length) (controls dir) (classify dir)) ee
    tag dest (before.append extra) (after.append extra) B (control_runs dir tag before after extra B h) hedge

/-- The actual exponent-dispatched stopped arithmetic jumps to the real
return guard on the full bank; no extra workspace is assumed blank. -/
theorem stopped_path (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (hN : N≤2^k) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (before after : Tapes (nodeTapes s c) 2) (extra : Tapes scratch 2) (B : ℕ)
    (h : HoareTime (CompactComplexSourceReadyStoppedLeafDispatch.program dir)
      (fun v => v=before) (fun v => v=after) B) :
    ∃ n≤B+1,FiniteFlowPath.Path (tableFamily (k:=k) dir stack returns events)
      (tableNext dir hN returns events re ee) (controlPCFor N length 1)
      (before.append extra) n 0 (after.append extra) :=
  control_path dir hN stack returns events re ee 1 0 before after extra B h (fun _ => rfl)

/-- Actual common-bank entry plus the real cyclic-table jump reaches the
shared stopped continuation, charging the jump and restoring every input tape. -/
theorem entry_stopped_path (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (hN : N≤2^k) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (v : Tapes (publicTapes s c) 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (extra : Tapes scratch 2) (D e : ℕ) (hD : 0<D) (h : Guard.Ready v)
    (hd : v.head Guard.dimension=1 ∧ v.tape Guard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head Guard.exponent=1 ∧ v.tape Guard.exponent=RadixZeroFill.encodedBinary (bits e))
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=true) :
    ∃ n≤Guard.setupCost D e+Guard.cleanupCost D e+4,
      FiniteFlowPath.Path (tableFamily (k:=k) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 0) ((bank v leaf work).append extra) n
        (controlPCFor N length 1) ((bank v leaf work).append extra) := by
  obtain ⟨n,hn,hr,hh,hc⟩ := CompactComplexSourceReadyNodeControls.entry_stopped v leaf work D e hD h hd he hs
  refine ⟨n+1,by omega,?_⟩
  exact entry_marker_path dir hN stack returns events re ee ((bank v leaf work).append extra) n
    ((((CompactComplexSourceReadyNodeControls.stoppedConfig v).extend leaf).extend work).extend extra)
    (extend_run (CompactComplexSourceReadyNodeControls.entry (s:=s) (c:=c)).2 extra hr)
    (extend_halt (CompactComplexSourceReadyNodeControls.entry (s:=s) (c:=c)).2 extra hh) true hc

/-- Actual common-bank entry plus the real cyclic-table jump reaches the
shared nonleaf continuation, charging the jump and restoring every input tape. -/
theorem entry_nonleaf_path (dir : CompactSpectatorLeafGuardOriginal.Direction)
    (hN : N≤2^k) (stack : Fin (tapes s c))
    (returns : Fin N → Σ q,Program (tapes s c) q 2)
    (events : Fin length → Σ q,Program (tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (v : Tapes (publicTapes s c) 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (work : Tapes 10 2) (extra : Tapes scratch 2) (D e : ℕ) (hD : 0<D) (h : Guard.Ready v)
    (hd : v.head Guard.dimension=1 ∧ v.tape Guard.dimension=RadixZeroFill.encodedBinary (bits D))
    (he : v.head Guard.exponent=1 ∧ v.tape Guard.exponent=RadixZeroFill.encodedBinary (bits e))
    (hs : Networks.ComplexRecursiveCallSchema.stopped D e=false) :
    ∃ n≤Guard.setupCost D e+Guard.cleanupCost D e+4,
      FiniteFlowPath.Path (tableFamily (k:=k) dir stack returns events)
        (tableNext dir hN returns events re ee) (controlPCFor N length 0) ((bank v leaf work).append extra) n
        (controlPCFor N length 2) ((bank v leaf work).append extra) := by
  obtain ⟨n,hn,hr,hh,hc⟩ := CompactComplexSourceReadyNodeControls.entry_nonleaf v leaf work D e hD h hd he hs
  refine ⟨n+1,by omega,?_⟩
  exact entry_marker_path dir hN stack returns events re ee ((bank v leaf work).append extra) n
    ((((CompactComplexSourceReadyNodeControls.nonleafConfig v).extend leaf).extend work).extend extra)
    (extend_run (CompactComplexSourceReadyNodeControls.entry (s:=s) (c:=c)).2 extra hr)
    (extend_halt (CompactComplexSourceReadyNodeControls.entry (s:=s) (c:=c)).2 extra hh) false hc



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
end IntegerMultBounds.Machine.CompactComplexSourceReadyFullNodeControls
