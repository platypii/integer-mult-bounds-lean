module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedSweep
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeaf

/-! Select the recursive or stopped worker from the tag on its scheduled record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout M8.RevMachine
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

private theorem replaceArchive {T w W : ℕ} [NeZero (prime^(w+1))] (bank : Fin 35 ↪ Fin T)
    (record next : List (Fin (prime+4))) (word : Fin ((prime^(w+1))^16*W) → ZMod 2) (S : Stacks T prime)
    (ready : RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size record
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word S) :
    RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size next
      SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0 word
      {S with R := Function.update S.R (bank 34) next} := by
  refine ⟨?_,?_,?_,?_,?_,Function.update_self ..,?_,?_,?_⟩
  all_goals try first
    | simpa [bank.injective.eq_iff] using ready.modulus
    | simpa [bank.injective.eq_iff] using ready.width
    | simpa [bank.injective.eq_iff] using ready.one
    | simpa [bank.injective.eq_iff] using ready.padded
    | simpa [bank.injective.eq_iff] using ready.clock
    | simpa [bank.injective.eq_iff] using ready.src
    | simpa [bank.injective.eq_iff] using ready.dst
  intro i hi
  have ne : i ≠ 34 := fun eq => (by decide : (34 : Fin 35) ∉ shearWork) (eq ▸ hi)
  simpa [Function.update_of_ne (bank.injective.ne ne)] using ready.scratch i hi

noncomputable def scheduledDispatch {T Q : ℕ} {P U : Type} (archive : Fin T) (large leaf : Pr P T Q prime U) : Pr P T Q prime U :=
  let select := Prog.act (.pop (.rt archive) (fun v o => { v with flag := symBit (o.getD blank) }) .done)
  let restore := fun b => Prog.act (.push (.rt archive) (fun _ => bitSymbol b) .done)
  select.seq (.cond (·.flag) (large.seq (restore true)) (leaf.seq (restore false)))

/-- The branch sees its original record. The caller gets its tagged record back
with three steps charged for reading, selecting and restoring the tag. -/
theorem scheduledDispatch_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (entry large leaf : P)
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
    (installed : body entry = scheduledDispatch (scheduledRecordPorts ports 34) (body large) (body leaf))
    (node child : Descriptor) (w W cutoff : ℕ) (record : List (Fin (prime+4)))
    (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)) (price : ℕ)
    (branch : ScheduledChildExec node child w W ports record position body
      (if cutoff < child.width then large else leaf) price) :
    ScheduledChildExec node child w W ports (bitSymbol (decide (cutoff < child.width)) :: record)
      position body entry (price+3) := by
  intro smaller u S word ready clean
  let bank := scheduledRecordPorts ports
  let active := decide (cutoff < child.width)
  let src := bank 34
  let D := {S with R := Function.update S.R src record}
  let v := {u with flag := active}
  have pop : Exec body (.act (.pop (.rt src) (fun v o => {v with flag := symBit (o.getD blank)}) .done))
      (mk u S) 1 (mk v D) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,src,bank,ready.archive,v,D,active,update_rt]
  have off (j : Fin (rowSwapBlock.tapes+35)) (hj : 35 ≤ j.val) : ports j ≠ src := by
    intro eq
    have h := congrArg Fin.val (ports.injective eq)
    change j.val = 34 at h
    omega
  obtain ⟨z,F,t,y,run,paid,user,out,free,frame,read⟩ := branch smaller v D word
    (replaceArchive bank _ _ _ _ ready) (fun j hj => ⟨(clean j hj).1,(Function.update_of_ne (off j hj) ..).trans (clean j hj).2⟩)
  let G := {F with R := Function.update F.R src (bitSymbol active :: record)}
  have push : Exec body (.act (.push (.rt src) (fun _ => bitSymbol active) .done)) (mk z F) 1 (mk z G) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,G,src,bank,out.archive,update_rt]
  refine ⟨z,G,1+(t+1+1),y,?_,by omega,user,replaceArchive bank _ _ _ _ out,?_,?_,read⟩
  · rw [installed]
    apply Exec.seq pop
    by_cases above : cutoff < child.width
    · apply Exec.cond_true (by simp [mk_var,v,active,above])
      simp only [active,above,decide_true,ite_true] at run push ⊢
      exact Exec.seq run push
    · apply Exec.cond_false (by simp [mk_var,v,active,above])
      simp only [active,above,decide_false,ite_false] at run push ⊢
      exact Exec.seq run push
  · intro j hj
    exact ⟨(free j hj).1,(Function.update_of_ne (off j hj) ..).trans (free j hj).2⟩
  · intro j away
    have ne : j ≠ src := (away ⟨34,by omega⟩).symm
    have keep := frame j away
    exact ⟨keep.1,(Function.update_of_ne ne ..).trans (keep.2.trans (Function.update_of_ne ne ..))⟩

/-- The MOVE table installs a single dispatcher per rank. Only the branch
above the cutoff needs a recursive execution witness. -/
theorem mixedMoveProgram [M8.Machine.Net] {T Q : ℕ} {P U : Type}
    (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T) (capacity : columnCapacity ≤ Q)
    (rank : ℕ) (positive : 0 < rank) :
    ∃ leafCode : Pr P T Q prime U, ∀ (body : P → Pr P T Q prime U) (entry large leaf : P),
      body leaf = leafCode →
      body entry = scheduledDispatch (scheduledRecordPorts ports 34) (body large) leafCode →
      ∀ (node child : Descriptor) (w W cutoff : ℕ), child.width = (w+1)*rank →
      ∀ position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W),
      (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) → 0 < W →
      let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
      ∀ (rate : ℝ) (recursiveTime : ℕ) (recursiveRecord : List (Fin (prime+4))), 163+core ≤ rate →
      let active := cutoff < child.width
      let record := if active then recursiveRecord else
        binSyms (CopyChildLayout.spectators child).size (CopyChildLayout.spectators child)
      let price := if active then recursiveTime else
        ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
      (active → ScheduledChildExec node child w W ports recursiveRecord position body large recursiveTime) →
      ScheduledChildExec node child w W ports (bitSymbol (decide active)::record) position body entry (price+3) := by
  obtain ⟨code,stopped⟩ := stoppedMoveProgram (P := P) (U := U) ports capacity rank positive
  refine ⟨code,?_⟩
  intro body entry large leaf installed dispatch node child w W cutoff width position packed pos core rate time archive room active record price recurse
  apply scheduledDispatch_exec body entry large leaf ports (installed ▸ dispatch) node child w W cutoff
  by_cases h : cutoff < child.width
  · simpa only [record,price,active,ite_eq_left h] using recurse h
  · simpa only [record,price,active,ite_eq_right h] using
      stopped body leaf installed node child w W width position packed pos rate room

open Certificates.PR589

/-- A mixed COPY worker preserves the supplied archive on either branch. -/
theorem mixedCopyProgram [M8.Machine.Net] :
    ∃ C : ℝ, ∀ {P U : Type} {T Q : ℕ} (ports : Fin (rowSwapBlock.tapes+35) ↪ Fin T)
      (fits : stoppedCopyMachine.1 ≤ Q) (body : P → Pr P T Q prime U) (entry large leaf : P),
      body leaf = stoppedCopyProgram ports fits →
      body entry = scheduledDispatch (scheduledRecordPorts ports 34) (body large) (body leaf) →
      ∀ (node : Descriptor) (n : Fin 9) (p : Fin 32 × Fin 5) (j : Fin Copy.lifecycles.length)
        (w W rows cutoff : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
      let child := scheduledChild prime node (copyChildPosition (n,p,j))
      ∀ (record : List (Fin (prime+4)))
        (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)),
      CopyIntervalPositions child (w+1) W position → 0 < W →
      ∀ (rate : ℝ) (recursiveTime : ℕ), C ≤ rate →
      let active := cutoff < child.width
      let price := if active then recursiveTime else
        ⌊(rate*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime child⌋₊
      (active → ScheduledChildExec node child w W ports record position body large recursiveTime) →
      ScheduledChildExec node child w W ports (bitSymbol (decide active)::record) position body entry (price+3) := by
  obtain ⟨C,stopped⟩ := stoppedCopyChild_budget
  refine ⟨C,?_⟩
  intro P U T Q ports fits body entry large leaf installed dispatch node n p j w W rows cutoff width split child record position coords pos rate time room active price recurse
  apply scheduledDispatch_exec body entry large leaf ports dispatch node child w W cutoff
  by_cases h : cutoff < child.width
  · simpa only [price,active,ite_eq_left h] using recurse h
  · simpa only [price,active,ite_eq_right h] using
      stopped ports fits body leaf installed node n p j w W rows width split record position coords pos rate room

/-- Labels private to a mixed worker, with the recursive procedure's labels
embedded in the active branch. -/
inductive WorkerLabel (P : Type)
  | entry | leaf | active (f : P)

noncomputable def workerTable {P U : Type} {T Q : ℕ} (archive : Fin T)
    (leaf : Pr (WorkerLabel P) T Q prime U) (large : P → Pr (WorkerLabel P) T Q prime U)
    (f : P) : WorkerLabel P → Pr (WorkerLabel P) T Q prime U
  | .entry => scheduledDispatch archive (large f) leaf
  | .leaf => leaf
  | .active g => large g

/-- Install mixed workers throughout the stage. The stage needs execution
witnesses only for the occurrences above the cutoff. -/
theorem mixedPackedSweep [M8.Machine.Net] (n : Fin 9) :
    ∃ (mt : StageRun → MoveIndex → ℕ) (ct : StageRun → CopyIndex → ℕ)
      (mr : ∀ p i, Fin (rowSwapBlock.tapes+35) ↪ Fin (mt p i))
      (cr : ∀ p j, Fin (rowSwapBlock.tapes+35) ↪ Fin (ct p j)) (states : ℕ) (leafRate : ℝ),
    ∀ {P U : Type} {Q : ℕ}, states ≤ Q →
    ∀ (ml : ∀ p i, P → Pr (WorkerLabel P) (mt p i) Q prime U) (mf : StageRun → MoveIndex → P)
      (cl : ∀ p j, P → Pr (WorkerLabel P) (ct p j) Q prime U) (cf : StageRun → CopyIndex → P),
    ∃ (mb : ∀ p i, WorkerLabel P → Pr (WorkerLabel P) (mt p i) Q prime U)
      (cb : ∀ p j, WorkerLabel P → Pr (WorkerLabel P) (ct p j) Q prime U) (coeff : StageRun → ℝ),
      (∀ p i f, mb p i (.active f) = ml p i f) ∧ (∀ p j f, cb p j (.active f) = cl p j f) ∧
      ∀ (node : Descriptor) (w B rows cutoff : ℕ), node.width = 64*(w+1) → node.rows = 142080*rows →
      node.beforeH = B*prime^(64*((w+1)*64)) →
      let K := node.beforeRows*rows*node.between*node.afterD
      let W := ((prime^(w+1))^112*B)*prime^(64*((w+1)*64))*K
      0 < W → ∀ rate : ℝ, leafRate ≤ rate →
      let mi := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
      let ci := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
      let child := scheduledChild prime node
      ∀ (record : Fin nodeChildren5.length → List (Fin (prime+4))) (budget : Fin nodeChildren5.length → ℕ),
      let price := fun i => (if cutoff < (child i).width then budget i else
        ⌊(rate*((child i).width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime (child i)⌋₊) + 3
      ∃ (mp : ∀ p i, Fin (volume prime (child (mi p i))) ≃ Fin ((prime^(w+1))^16*W))
        (cp : ∀ p j, Fin (volume prime (child (ci p j))) ≃ Fin ((prime^(w+1))^16*W)),
      (∀ p i h, (mp p i h).val = (CopyChildLayout.packActive (child (mi p i)) h).val) ∧
      (∀ p j, CopyIntervalPositions (child (ci p j)) (w+1) W (cp p j)) ∧
      ∃ (L : Type) (tapes : StageRun → ℕ) (body : ∀ p, L → Pr L (tapes p) Q prime U),
        PackedStageExecution (w := w+1) (B := B) (K := K) n tapes body coeff (fun time =>
          (∀ i : Fin nodeChildren5.length, time i.val = price i) ∧
          (∀ p i, let k := mi p i; cutoff < (child k).width →
            ScheduledChildExec node (child k) w W (mr p i) (record k) (mp p i) (mb p i) (.active (mf p i)) (budget k)) ∧
          (∀ p j, let k := ci p j; cutoff < (child k).width →
            ScheduledChildExec node (child k) w W (cr p j) (record k) (cp p j) (cb p j) (.active (cf p j)) (budget k))) := by
  classical
  obtain ⟨mt,ct,mr,cr,mT,cT,mBank,cBank,states,build⟩ := scheduledInvocationFamily n
  obtain ⟨copyRate,copy⟩ := mixedCopyProgram
  let core : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
  refine ⟨mt,ct,mr,cr,max states (max columnCapacity stoppedCopyMachine.1),max (163+core) copyRate,?_⟩
  intro P U Q room ml mf cl cf
  have caps := (le_max_right _ _).trans room
  let mi := fun (p : StageRun) (i : MoveIndex) => phaseChildPositions.choose (n,p,i)
  let ci := fun (p : StageRun) (j : CopyIndex) => copyChildPosition (n,p,j)
  choose leaf move using fun (p : StageRun) (i : MoveIndex) =>
    mixedMoveProgram (P := WorkerLabel P) (U := U) (mr p i) ((le_max_left _ _).trans caps)
      (nodeChildren5[(mi p i).val]) (nodeChildren5_bounds (mi p i)).1
  let mb := fun p i => workerTable (scheduledRecordPorts (mr p i) 34) (leaf p i) (ml p i) (mf p i)
  let cb := fun p j => workerTable (scheduledRecordPorts (cr p j) 34)
    (stoppedCopyProgram (cr p j) ((le_max_right _ _).trans caps)) (cl p j) (cf p j)
  obtain ⟨coeff,stage⟩ := build ((le_max_left _ _).trans room) mb (fun _ _ => .entry) cb (fun _ _ => .entry)
  refine ⟨mb,cb,coeff,fun _ _ _ => rfl,fun _ _ _ => rfl,?_⟩
  intro node w B rows cutoff width split label K W pos rate large _ _ child record budget price
  let active := fun k => cutoff < (child k).width
  let mrec := fun p i => let k := mi p i; let s := CopyChildLayout.spectators (child k)
                         bitSymbol (decide (active k)) :: (if active k then record k else binSyms s.size s)
  let crec := fun p j => let k := ci p j; bitSymbol (decide (active k)) :: record k
  obtain ⟨mp,cp,banks,mc,cc,T,fan,bank,run⟩ := stage node w B rows width split label pos mrec crec
  refine ⟨mp,cp,mc,cc,_,fun p => (banks p).tapes,fun p => (banks p).body (mBank p) (cBank p) (mb p) (cb p),T,fan,bank,?_⟩
  intro scratch owner worker host blocks V time ready
  apply run time
  constructor
  · intro p i
    rw [ready.1 (mi p i)]
    have shape : (child (mi p i)).width = (w+1)*nodeChildren5[(mi p i).val] := by
      change nodeChildren5[(mi p i).val]*(node.width/64) = _
      rw [width,Nat.mul_div_cancel_left _ (by decide),Nat.mul_comm]
    exact move p i (mb p i) .entry (.active (mf p i)) .leaf rfl rfl node _ w W cutoff shape
      (mp p i) (mc p i) pos rate _ _ ((le_max_left _ _).trans large) (ready.2.1 p i)
  · intro p j
    rw [ready.1 (ci p j)]
    exact copy (cr p j) _ (cb p j) .entry (.active (cf p j)) .leaf rfl rfl node n p j w W rows cutoff
      width split _ (cp p j) (cc p j) pos rate _ ((le_max_right _ _).trans large) (ready.2.2 p j)

end IntegerMultBounds.MathlibTM2.M6.BitNode
