import IntegerMultBounds.Machine.CompactSpectatorStoppedReturnFlow
import IntegerMultBounds.Machine.CompactComplexControllerChildReturn

/-! Actual internal-child entry and return blocks occupy literal continuations
of the stopped-leaf cyclic table. Entry saves parent descriptors, pushes the
actual table return PC, descends the exponent, and installs selected child
headers. Return erases child headers, restores parent descriptors and exponent.
No execution of the intervening recursive child is assumed here. -/
namespace IntegerMultBounds.Machine.CompactSpectatorInternalChildFlow
noncomputable section
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open ActiveRepairRankHeadersCommands (State put)
open ActivePrefixStageHeadersData (initial)
open CompactComplexControllerChildPrefix (native data)
open SharedPlacementAlphabet (setTape)
variable {w r N : ℕ}

abbrev coreCount (w : ℕ) := CompactComplexControllerNativeFrame.tapes (w+2)
abbrev total (w : ℕ) := CompactSpectatorStoppedLeafCaller.total (w:=w)
theorem count_eq : coreCount w=CompactSpectatorLeafPlacement.callerCount w := by
  unfold coreCount CompactComplexControllerNativeFrame.tapes CompactSpectatorLeafPlacement.callerCount
  omega

def pad (v : Tapes (coreCount w) 2) : Tapes (total w) 2 :=
  ((v.reindex (finCongr count_eq)).append (SharedBank.empty CompactSpectatorLeafOriginal.tapes 2)).append
    (SharedBank.empty 43 2)
def framed {q : ℕ} (P : Program (coreCount w) q 2) : Program (total w) q 2 :=
  extend (extend (reindex P (finCongr count_eq)) CompactSpectatorLeafOriginal.tapes) 43

theorem framed_runs {q b : ℕ} {P : Program (coreCount w) q 2} {v z : Tapes (coreCount w) 2}
    (h : HoareTime P (fun x => x=v) (fun x => x=z) b) :
    HoareTime (framed P) (fun x => x=pad v) (fun x => x=pad z) b :=
  hoare_extend_eq (hoare_extend_eq (hoare_reindex_eq h (finCongr count_eq))
    (SharedBank.empty CompactSpectatorLeafOriginal.tapes 2)) (SharedBank.empty 43 2)

def pcSlot (stack : Fin (w+2)) : Fin (total w) :=
  Fin.castAdd 43 (Fin.castAdd CompactSpectatorLeafOriginal.tapes
    (finCongr count_eq (CompactComplexControllerNativeFrame.storageSlot stack)))

def returnPC : Fin (N+2) := ⟨1,by omega⟩

def pushed (storage : Tapes (w+2) 2) (stack : Fin (w+2)) (hN : N+2≤2^r) :=
  setTape storage stack
    (FiniteReturnStack.wordPart (storage.tape stack) (storage.head stack)
      (FiniteReturnStack.address hN (returnPC (N:=N))) r le_rfl) (storage.head stack+r)

def pushProgram (stack : Fin (w+2)) (hN : N+2≤2^r) :=
  FiniteReturnStackAt.pushProgram (a:=2) (CompactComplexControllerNativeFrame.storageSlot stack)
    (FiniteReturnStack.address hN (returnPC (N:=N)))

private theorem setTape_append_right {l u a : ℕ} (v : Tapes l a) (z : Tapes u a)
    (i : Fin u) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.append z) (Fin.natAdd l i) f p=v.append (setTape z i f p) := by
  unfold setTape Tapes.append
  congr 1 <;> funext j <;> induction j using Fin.addCases <;> simp [Function.update_apply,Fin.ext_iff]
  all_goals intro h; omega

private theorem push_runs (stack : Fin (w+2)) (hN : N+2≤2^r)
    (control : Tapes 43 2) (queue : Tapes 1 2) (payload : Tapes 66 2) (storage : Tapes (w+2) 2) :
    HoareTime (pushProgram stack hN)
      (fun v => v=CompactComplexControllerNativeFrame.bank control queue payload storage)
      (fun v => v=CompactComplexControllerNativeFrame.bank control queue payload (pushed storage stack hN)) r := by
  have h := FiniteReturnStackAt.push_hoare (a:=2) (CompactComplexControllerNativeFrame.storageSlot stack)
    (FiniteReturnStack.address hN (returnPC (N:=N)))
    (CompactComplexControllerNativeFrame.bank control queue payload storage)
  apply h.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  unfold FiniteReturnStackAt.pushed pushed CompactComplexControllerNativeFrame.bank
    CompactComplexControllerNativeFrame.storageSlot
  rw [setTape_append_right,setTape_append_right,setTape_append_right]
  simp only [Tapes.append,Fin.addCases_right]

private theorem setTape_reindex {l u a : ℕ} (e : Fin l ≃ Fin u) (v : Tapes l a)
    (i : Fin l) (f : ℤ → Fin (a+4)) (p : ℤ) :
    setTape (v.reindex e) (e i) f p=(setTape v i f p).reindex e := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals obtain ⟨j,rfl⟩ := e.surjective j
  all_goals simp [setTape,Tapes.reindex,Function.update_apply,e.injective.eq_iff]

private theorem pad_setTape (v : Tapes (coreCount w) 2) (i : Fin (coreCount w))
    (f : ℤ → Fin 6) (p : ℤ) :
    setTape (pad v) (Fin.castAdd 43 (Fin.castAdd CompactSpectatorLeafOriginal.tapes
      (finCongr count_eq i))) f p=pad (setTape v i f p) := by
  unfold pad
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,setTape_reindex]

private theorem pad_pc_tape (v : Tapes (coreCount w) 2) (stack : Fin (w+2)) :
    (pad v).tape (pcSlot stack)=v.tape (CompactComplexControllerNativeFrame.storageSlot stack) := by
  simp only [pad,pcSlot,Tapes.append,Fin.addCases_left,Tapes.reindex,Equiv.symm_apply_apply]
private theorem pad_pc_head (v : Tapes (coreCount w) 2) (stack : Fin (w+2)) :
    (pad v).head (pcSlot stack)=v.head (CompactComplexControllerNativeFrame.storageSlot stack) := by
  simp only [pad,pcSlot,Tapes.append,Fin.addCases_left,Tapes.reindex,Equiv.symm_apply_apply]

/-- The prefix's actual saved storage is precisely the physical full-bank
return frame consumed by the cyclic guard and decoder. -/
theorem pad_pushed (stack : Fin (w+2)) (hN : N+2≤2^r)
    (control : Tapes 43 2) (queue : Tapes 1 2) (payload : Tapes 66 2) (storage : Tapes (w+2) 2) :
    FiniteReturnStackAt.pushed (pcSlot stack) (FiniteReturnStack.address hN (returnPC (N:=N)))
      (pad (CompactComplexControllerNativeFrame.bank control queue payload storage))=
    pad (CompactComplexControllerNativeFrame.bank control queue payload (pushed storage stack hN)) := by
  unfold FiniteReturnStackAt.pushed
  rw [pad_pc_tape,pad_pc_head]
  unfold pcSlot
  rw [pad_setTape]
  apply congrArg pad
  unfold pushed CompactComplexControllerNativeFrame.bank CompactComplexControllerNativeFrame.storageSlot
  rw [setTape_append_right,setTape_append_right,setTape_append_right]
  simp only [Tapes.append,Fin.addCases_right]

/-- The pushed code targets continuation1 of the very same cyclic table,
whose continuation bank starts after guard/pop/forward-leaf/inverse-leaf. -/
def callBlock (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (slot : Fin arity) :
    Σ q,Program (total w) q 2 :=
  ⟨_,framed (seq (seq (seq (CompactComplexControllerHeaderStack.saveProgram headerStack)
    (pushProgram pcStack hN)) CompactComplexControllerExponent.program)
      (CompactComplexControllerNativeFrame.program (CompactComplexChildHeadersData.placedProgram slot)))⟩

def restore (headerStack : Fin (w+2)) : Σ q,Program (total w) q 2 :=
  ⟨_,framed (CompactComplexControllerChildReturn.program headerStack).2⟩

def callCost {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ) :=
  CompactChildHeadersStack.cost (data (CompactComplexChildHeadersData.parent rho visit hactive pair))+
    r+20*(k+3)+103+CompactChildHeadersArithmetic.scheduleCost (CompactComplexChildHeadersData.schedule slot)
      (initial (CompactComplexChildHeadersData.parent rho visit hactive pair) rows)

def returnCost {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) :=
  2*((data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 0).length+
    (data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 1).length+
    (data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 2).length)+
      CompactChildHeadersStack.cost (data (CompactComplexChildHeadersData.parent rho visit hactive pair))+
        2*(k+3)+16

theorem prefix_runs {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (w+2) 2) :
    HoareTime (callBlock headerStack pcStack hN slot).2
      (fun v => v=pad (CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
        (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage))
      (fun v => v=pad (CompactComplexControllerNativeFrame.bank
        (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
        (native (CompactComplexChildHeadersData.child rho visit hactive pair slot) rows tail)
        (pushed (CompactComplexControllerHeaderStack.saved storage headerStack
          (data (CompactComplexChildHeadersData.parent rho visit hactive pair))) pcStack hN)))
      (callCost (r:=r) rho visit hactive pair slot rows) := by
  let parent := CompactComplexChildHeadersData.parent rho visit hactive pair
  let headers := CompactComplexControllerHeaderStack.saved storage headerStack (data parent)
  let stores := pushed headers pcStack hN
  have hs := CompactComplexControllerHeaderStack.save headerStack (ActiveRepairRankHeadersCommands.bank st) queue
    (native parent rows tail) storage (data parent)
    (by intro i; fin_cases i <;> simp [native,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,initial,ActivePrefixStageHeadersData.originalValues,
      Tapes.append,Fin.addCases,data,BinaryDescriptorStackRoundtrip.descriptor_encoded])
    (by intro i; fin_cases i <;> simp [native,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,initial,ActivePrefixStageHeadersData.originalValues,Tapes.append,Fin.addCases])
  have hp := push_runs pcStack hN (ActiveRepairRankHeadersCommands.bank st) queue (native parent rows tail) headers
  have hd := CompactComplexControllerExponent.descend st (k+2) (by omega) h1 queue (native parent rows tail) stores
  rw [show k+2-1=k+1 by omega] at hd
  have hc := CompactComplexControllerNativeFrame.runs
    (CompactComplexChildHeadersData.runs_framed (a:=2) rho visit hactive pair slot rows tail)
    (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue stores
  have h := framed_runs (((hs.seq hp).seq hd).seq hc)
  exact h.consequence (fun _ h => h) (fun _ h => h) (by dsimp only [callCost,parent]; omega)

theorem restore_runs {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack : Fin (w+2)) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (w+2) 2)
    (hb : ∀ z,storage.head headerStack≤z → storage.tape headerStack z=blank) :
    HoareTime (restore headerStack).2
      (fun v => v=pad (CompactComplexControllerNativeFrame.bank
        (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
        (native (CompactComplexChildHeadersData.child rho visit hactive pair slot) rows tail)
        (CompactComplexControllerHeaderStack.saved storage headerStack
          (data (CompactComplexChildHeadersData.parent rho visit hactive pair)))))
      (fun v => v=pad (CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
        (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage))
      (returnCost rho visit hactive pair slot) :=
  framed_runs (CompactComplexControllerChildReturn.runs rho visit hactive pair slot rows headerStack st h1 queue tail storage hb)


/-- Two concrete internal continuations precede all caller-supplied blocks.
The saved return code is1; finite-flow embedding adds exactly four. -/
def tableStates (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (slot : Fin arity)
    (rest : Fin N → ℕ) : Fin (N+2) → ℕ :=
  Fin.cases (callBlock headerStack pcStack hN slot).1 (Fin.cases (restore headerStack).1 rest)
def tableFamily (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (slot : Fin arity)
    (rest : Fin N → ℕ) (blocks : ∀ pc,Program (total w) (rest pc) 2) :
    ∀ pc,Program (total w) (tableStates headerStack pcStack hN slot rest pc) 2 :=
  Fin.cases (callBlock headerStack pcStack hN slot).2 (Fin.cases (restore headerStack).2 blocks)
def tableEdges (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (slot : Fin arity)
    (rest : Fin N → ℕ) (childEntry afterChild : Fin ((N+2)+4))
    (edges : ∀ pc,Fin (rest pc) → Option (Fin ((N+2)+4))) :
    ∀ pc,Fin (tableStates headerStack pcStack hN slot rest pc) → Option (Fin ((N+2)+4)) :=
  Fin.cases (fun _ => some childEntry) (Fin.cases (fun _ => some afterChild) edges)
def program (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (slot : Fin arity)
    (rest : Fin N → ℕ) (blocks : ∀ pc,Program (total w) (rest pc) 2)
    (childEntry afterChild : Fin ((N+2)+4))
    (edges : ∀ pc,Fin (rest pc) → Option (Fin ((N+2)+4))) (entry : Fin ((N+2)+4)) :=
  CompactSpectatorStoppedLeafFlow.program hN (pcSlot pcStack)
    (tableStates headerStack pcStack hN slot rest) (tableFamily headerStack pcStack hN slot rest blocks)
    (tableEdges headerStack pcStack hN slot rest childEntry afterChild edges) entry

private theorem continuation_ready {M : ℕ} (hM : M≤2^r) (stack : Fin (total w))
    (rest : Fin M → ℕ) (blocks : ∀ pc,Program (total w) (rest pc) 2)
    (edges : ∀ pc,Fin (rest pc) → Option (Fin (M+4))) (entry dest : Fin (M+4))
    (idx : Fin M) (v z : Tapes (total w) 2) (b : ℕ)
    (he : ∀ st,edges idx st=some dest)
    (hh : HoareTime (blocks idx) (fun x => x=v) (fun x => x=z) b) :
    ∃ n,n≤b+1 ∧ run (CompactSpectatorStoppedLeafFlow.program hM stack rest blocks edges entry) n
      ((v.start (blocks idx)).mapState
        (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r) rest) idx.succ.succ.succ.succ))=
      some ((z.start (CompactSpectatorStoppedLeafFlow.family stack rest blocks dest)).mapState
        (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r) rest) dest)) := by
  obtain ⟨n,c,hn,hr,hhalt,hpost⟩ := hh v rfl
  change c.tapes=z at hpost
  have hed : CompactSpectatorStoppedLeafFlow.next (w:=w) hM rest edges idx.succ.succ.succ.succ c.state=some dest := by
    change edges idx c.state=some dest
    exact he c.state
  have ht := FiniteFlow.block_then_jump (CompactSpectatorStoppedLeafFlow.family stack rest blocks)
    (CompactSpectatorStoppedLeafFlow.next (w:=w) hM rest edges) entry idx.succ.succ.succ.succ dest v n c hr hhalt hed
  change run (CompactSpectatorStoppedLeafFlow.program hM stack rest blocks edges entry) (n+1)
    ((v.start (blocks idx)).mapState (FiniteFlow.embed
      (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r) rest) idx.succ.succ.succ.succ))=
    some ((c.tapes.start (CompactSpectatorStoppedLeafFlow.family stack rest blocks dest)).mapState
      (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r) rest) dest)) at ht
  rw [hpost] at ht
  exact ⟨n+1,by omega,ht⟩

/-- Actual child-entry block finishes at the child-entry PC of the same cyclic
machine. All parent save, literal push, exponent and child-header costs are paid. -/
theorem call_ready {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (w+2) 2)
    (rest : Fin N → ℕ) (blocks : ∀ pc,Program (total w) (rest pc) 2)
    (childEntry afterChild : Fin ((N+2)+4))
    (edges : ∀ pc,Fin (rest pc) → Option (Fin ((N+2)+4))) (entry : Fin ((N+2)+4)) :
    ∃ n,n≤callCost (r:=r) rho visit hactive pair slot rows+1 ∧
      run (program headerStack pcStack hN slot rest blocks childEntry afterChild edges entry) n
        (((pad (CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
          (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage)).start
            (callBlock headerStack pcStack hN slot).2).mapState
              (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r)
                (tableStates headerStack pcStack hN slot rest)) 4))=
        some (((pad (CompactComplexControllerNativeFrame.bank
          (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
          (native (CompactComplexChildHeadersData.child rho visit hactive pair slot) rows tail)
          (pushed (CompactComplexControllerHeaderStack.saved storage headerStack
            (data (CompactComplexChildHeadersData.parent rho visit hactive pair))) pcStack hN))).start
          (CompactSpectatorStoppedLeafFlow.family (pcSlot pcStack)
            (tableStates headerStack pcStack hN slot rest) (tableFamily headerStack pcStack hN slot rest blocks) childEntry)).mapState
          (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r)
            (tableStates headerStack pcStack hN slot rest)) childEntry)) := by
  exact continuation_ready hN (pcSlot pcStack) (tableStates headerStack pcStack hN slot rest)
    (tableFamily headerStack pcStack hN slot rest blocks)
    (tableEdges headerStack pcStack hN slot rest childEntry afterChild edges)
    entry childEntry 0 _ _ _ (fun _ => rfl) (prefix_runs rho visit hactive pair slot rows headerStack pcStack hN st h1 queue tail storage)


/-- The retained literal PC physically selects this table's restore block;
its erased stack frame is paid, and no restore-execution callback is needed. -/
theorem return_to_restore (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (slot : Fin arity)
    (rest : Fin N → ℕ) (blocks : ∀ pc,Program (total w) (rest pc) 2)
    (childEntry afterChild : Fin ((N+2)+4))
    (edges : ∀ pc,Fin (rest pc) → Option (Fin ((N+2)+4))) (entry : Fin ((N+2)+4))
    (v : Tapes (total w) 2)
    (hf : ∀ j<r,v.tape (pcSlot pcStack) (v.head (pcSlot pcStack)+j)=blank) :
    run (program headerStack pcStack hN slot rest blocks childEntry afterChild edges entry) (r+5)
      (((FiniteReturnStackAt.pushed (pcSlot pcStack) (FiniteReturnStack.address hN (returnPC (N:=N))) v).start
        (FiniteReturnGuard.program (pcSlot pcStack))).mapState
          (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r)
            (tableStates headerStack pcStack hN slot rest)) 0))=
      some ((v.start (restore headerStack).2).mapState
        (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r)
          (tableStates headerStack pcStack hN slot rest)) (returnPC (N:=N)).succ.succ.succ.succ)) := by
  have hr : 0<r := by
    by_contra h
    have hz : r=0 := by omega
    simp only [hz,pow_zero] at hN
    omega
  have h := CompactSpectatorStoppedReturnFlow.return_ready hN hr (pcSlot pcStack)
    (tableStates headerStack pcStack hN slot rest) (tableFamily headerStack pcStack hN slot rest blocks)
    (tableEdges headerStack pcStack hN slot rest childEntry afterChild edges) entry (returnPC (N:=N))
    (FiniteReturnStackAt.pushed (pcSlot pcStack) (FiniteReturnStack.address hN (returnPC (N:=N))) v)
    (v.tape (pcSlot pcStack)) (v.head (pcSlot pcStack))
    (by simp only [FiniteReturnStackAt.pushed,setTape,Function.update_self])
    (by simp only [FiniteReturnStackAt.pushed,setTape,Function.update_self]) hf
  simp only [FiniteReturnStackAt.pushed,SharedPlacementAlphabet.setTape_setTape,
    SharedPlacementAlphabet.setTape_self] at h
  have hfam : tableFamily headerStack pcStack hN slot rest blocks (returnPC (N:=N))=
      (restore headerStack).2 := by
    change tableFamily headerStack pcStack hN slot rest blocks (0 : Fin (N+1)).succ=(restore headerStack).2
    rfl
  rw [hfam] at h
  exact h

/-- After the physical PC decoder, the actual restore block erases child
headers and restores parent descriptors/exponent before the next continuation. -/
theorem restore_ready {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (w+2) 2)
    (hb : ∀ z,storage.head headerStack≤z → storage.tape headerStack z=blank)
    (rest : Fin N → ℕ) (blocks : ∀ pc,Program (total w) (rest pc) 2)
    (childEntry afterChild : Fin ((N+2)+4))
    (edges : ∀ pc,Fin (rest pc) → Option (Fin ((N+2)+4))) (entry : Fin ((N+2)+4)) :
    ∃ n,n≤returnCost rho visit hactive pair slot+1 ∧
      run (program headerStack pcStack hN slot rest blocks childEntry afterChild edges entry) n
        (((pad (CompactComplexControllerNativeFrame.bank
          (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
          (native (CompactComplexChildHeadersData.child rho visit hactive pair slot) rows tail)
          (CompactComplexControllerHeaderStack.saved storage headerStack
            (data (CompactComplexChildHeadersData.parent rho visit hactive pair))))).start
          (restore headerStack).2).mapState
          (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r)
            (tableStates headerStack pcStack hN slot rest)) (returnPC (N:=N)).succ.succ.succ.succ))=
        some (((pad (CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
          (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage)).start
          (CompactSpectatorStoppedLeafFlow.family (pcSlot pcStack) (tableStates headerStack pcStack hN slot rest)
            (tableFamily headerStack pcStack hN slot rest blocks) afterChild)).mapState
          (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r)
            (tableStates headerStack pcStack hN slot rest)) afterChild)) := by
  exact continuation_ready hN (pcSlot pcStack) (tableStates headerStack pcStack hN slot rest)
    (tableFamily headerStack pcStack hN slot rest blocks)
    (tableEdges headerStack pcStack hN slot rest childEntry afterChild edges)
    entry afterChild (returnPC (N:=N)) _ _ _ (fun _ => rfl)
    (restore_runs rho visit hactive pair slot rows headerStack st h1 queue tail storage hb)


/-- Complete physical return: occupied guard, actual PC pop/erase, actual
child-header erasure, parent-header restore, exponent ascent and final jump.
The supplied tail is the child's computed payload; it is preserved literally. -/
theorem returned_ready {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack pcStack : Fin (w+2)) (hN : N+2≤2^r) (hsep : pcStack≠headerStack)
    (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 2) (tail : Tapes 23 2) (storage : Tapes (w+2) 2)
    (hb : ∀ z,storage.head headerStack≤z → storage.tape headerStack z=blank)
    (hpc : ∀ j<r,storage.tape pcStack (storage.head pcStack+j)=blank)
    (rest : Fin N → ℕ) (blocks : ∀ pc,Program (total w) (rest pc) 2)
    (childEntry afterChild : Fin ((N+2)+4))
    (edges : ∀ pc,Fin (rest pc) → Option (Fin ((N+2)+4))) (entry : Fin ((N+2)+4)) :
    let parent := CompactComplexChildHeadersData.parent rho visit hactive pair
    let child := CompactComplexChildHeadersData.child rho visit hactive pair slot
    let headers := CompactComplexControllerHeaderStack.saved storage headerStack (data parent)
    let v := pad (CompactComplexControllerNativeFrame.bank
      (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue (native child rows tail)
      (pushed headers pcStack hN))
    let z := pad (CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
      (native parent rows tail) storage)
    ∃ n,n≤r+6+returnCost rho visit hactive pair slot ∧
      run (program headerStack pcStack hN slot rest blocks childEntry afterChild edges entry) n
        ((v.start (FiniteReturnGuard.program (pcSlot pcStack))).mapState
          (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r)
            (tableStates headerStack pcStack hN slot rest)) 0))=
        some ((z.start (CompactSpectatorStoppedLeafFlow.family (pcSlot pcStack)
          (tableStates headerStack pcStack hN slot rest) (tableFamily headerStack pcStack hN slot rest blocks) afterChild)).mapState
          (FiniteFlow.embed (CompactSpectatorStoppedLeafFlow.states (w:=w) (r:=r)
            (tableStates headerStack pcStack hN slot rest)) afterChild)) := by
  dsimp only
  let parent := CompactComplexChildHeadersData.parent rho visit hactive pair
  let child := CompactComplexChildHeadersData.child rho visit hactive pair slot
  let headers := CompactComplexControllerHeaderStack.saved storage headerStack (data parent)
  let base := CompactComplexControllerNativeFrame.bank
    (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue (native child rows tail) headers
  have hblank : ∀ j<r,(pad base).tape (pcSlot pcStack) ((pad base).head (pcSlot pcStack)+j)=blank := by
    intro j hj
    rw [pad_pc_tape,pad_pc_head]
    simpa only [base,CompactComplexControllerNativeFrame.bank,CompactComplexControllerNativeFrame.storageSlot,
      Tapes.append,Fin.addCases_right,headers,CompactComplexControllerHeaderStack.saved,setTape,
      Function.update_of_ne hsep] using hpc j hj
  have hg := return_to_restore headerStack pcStack hN slot rest blocks childEntry afterChild edges entry (pad base) hblank
  dsimp only [base] at hg
  rw [pad_pushed] at hg
  obtain ⟨n,hn,hr⟩ := restore_ready rho visit hactive pair slot rows headerStack pcStack hN st h1 queue tail storage hb
    rest blocks childEntry afterChild edges entry
  refine ⟨r+5+n,by omega,?_⟩
  rw [run_add,hg]
  simp only [Option.bind_some]
  exact hr

end
end IntegerMultBounds.Machine.CompactSpectatorInternalChildFlow
