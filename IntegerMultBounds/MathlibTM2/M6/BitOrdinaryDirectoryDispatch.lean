module

public import IntegerMultBounds.MathlibTM2.Host.StateTransport
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryChildCounts
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Select a scheduled directory branch using the physical child width and cutoff. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open FlatCoordinateLayout LabelTraversal Matrix M8.Exchange IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- The scanner carries the saved cutoff in register 40 and the unary width in
register 45. The comparison uses eight private tapes, all blank at child entry. -/
def chartCutoffBank {n : ℕ} (K T : ℕ) (room : 8 ≤ T)
    (replay : Fin (66+((K+1)+3+T)) ↪ Fin n) : Fin 10 ↪ Fin n :=
  (⟨fun j => ⟨if j.val = 0 then 45 else if j.val = 1 then 40 else 66+(K+1)+3+(j.val-2),
      by split_ifs <;> omega⟩,by
    intro i j eq
    apply Fin.ext
    have h := congrArg Fin.val eq
    dsimp only at h
    repeat' split at h
    all_goals omega⟩ : Fin 10 ↪ Fin (66+((K+1)+3+T))).trans replay

private theorem chartCutoffBank_scratch {n : ℕ} (K T : ℕ) (room : 8 ≤ T)
    (replay : Fin (66+((K+1)+3+T)) ↪ Fin n) (j : Fin 10) (high : 2 ≤ j.val) :
    chartCutoffBank K T room replay j = replay (stoppedChartPrivate (K+1) T ⟨j.val-2,by omega⟩) := by
  apply congrArg replay
  apply Fin.ext
  change (if j.val = 0 then _ else if j.val = 1 then _ else _) = _
  rw [ite_eq_right (show j.val ≠ 0 by omega),ite_eq_right (show j.val ≠ 1 by omega)]
  rfl

/-- The cutoff test restores all stacks before entering the selected branch. -/
private theorem chartCutoff_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (cmp : Fin 10 ↪ Fin T) (rank w L cutoff : ℕ) (cutFits : cutoff < 2^L)
    (fits : ((w+1)*rank).size ≤ L) (large leaf : Pr P T Q prime U)
    (a : HS T Q prime U) (S : Stacks T prime)
    (clock : (S.R (cmp 0)).length = w) (word : S.R (cmp 1) = binSyms L cutoff)
    (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (cmp j) = [])
    (result : Stacks T prime → Prop) (budget : ℝ)
    (selected : ∀ z : HS T Q prime U, ∃ y B, ∃ k : ℕ, y.user = z.user ∧ (k : ℝ) ≤ budget ∧
      Exec body (if cutoff < (w+1)*rank then large else leaf) (mk z S) k (mk y B) ∧ result B) :
    ∃ y B, ∃ k : ℕ, y.user = a.user ∧ (k : ℝ) ≤ (4*w+23*((w+1)*rank)+22*L+51 : ℕ)+budget ∧
      Exec body ((ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7))) large leaf))
        (mk a S) k (mk y B) ∧ result B := by
  obtain ⟨z,m,user,flag,time,test⟩ := ordinaryCutoffTest_exec body cmp rank w L cutoff cutFits fits a S clock word empty
  obtain ⟨y,B,k,same,paid,run,out⟩ := selected z
  have branch : Exec body (.cond (fun z => symBit (z.scan (cmp 7))) large leaf) (mk z S) (k+1) (mk y B) := by
    by_cases active : cutoff < (w+1)*rank
    · exact Exec.cond_true (by simp [mk_var,flag,active]) (by simpa only [ite_eq_left active] using run)
    · exact Exec.cond_false (by simp [mk_var,flag,active]) (by simpa only [ite_eq_right active] using run)
  refine ⟨y,B,m+(k+1),same.trans user,?_,Exec.seq test branch,out⟩
  have testPaid : ((m+1 : ℕ) : ℝ) ≤ ((4*w+23*((w+1)*rank)+22*L+51 : ℕ) : ℝ) := by exact_mod_cast (by omega : m+1 ≤ _)
  push_cast at testPaid ⊢
  linarith

/-- The chart and recursive procedures share a tape bank. Chart calls retain
their original labels on the left, and recursion uses the labels on the right. -/
def recursiveChartTable {T Q : ℕ} {P R U : Type}
    (chart : P → Pr P T Q prime U) (recursive : R → Pr (P ⊕ R) T Q prime U) :
    P ⊕ R → Pr (P ⊕ R) T Q prime U :=
  Sum.elim (fun f => stateMapProg id id Sum.inl (chart f)) recursive

private theorem stateMapAct_id {K σ : Type} {Γ : K → Type} (a : Action Γ σ) :
    stateMapAct id id a = a := by
  induction a <;> simp_all [stateMapAct]

/-- Renaming an installed procedure preserves its tape placement and composes
the two maps on callees. -/
private theorem renamePlaced {K T Q : ℕ} {P G R U : Type} (bank : Fin K ↪ Fin T)
    (label : P → G) (includeLabel : G → R) (p : Pr P K Q prime U) :
    stateMapProg id id includeLabel (embProg bank label p) = embProg bank (includeLabel ∘ label) p := by
  induction p <;> simp_all [embProg,stateMapProg,stateMapAct_id]

/-- The recursive table installs both placements used by the generated scan:
incoming on the chart bank and outgoing on the saved replay bank. -/
theorem recursiveChartTable_scan [M8.Machine.Net] {K : ℕ} {P C R U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ K+1)
    (localBody : P → Pr P (66+K) columnCapacity prime U) (child : C → Pr C ((66+K)+1) columnCapacity prime U) :
    let T := 66+(K+1)
    let place := directoryChartPlacement T
    let bank := directoryOrdinaryBank room
    let slots := replaySlots.trans (Fin.castAddEmb K)
    let saved := (Fin.castLEEmb (by decide : 4 ≤ 6)).trans (directoryChartReplay T)
    let outgoing := directoryOutgoingPlacement bank place slots saved (fun _ _ => directoryChartPlacement_ne_work _ _)
    ∀ recursive : R → Pr ((P ⊕ (P ⊕ C)) ⊕ R) ((T+10)+5) columnCapacity prime U,
      let body := recursiveChartTable (directoryChartHost room localBody child) recursive
      (∀ f, body (.inl (.inl f)) = embProg place (Sum.inl ∘ Sum.inl)
        (embProg (Fin.castAdd 5) id (embProg bank id (localBody f)))) ∧
      (∀ f, body (.inl (.inr (.inl f))) = embProg outgoing (Sum.inl ∘ (Sum.inr ∘ Sum.inl))
        (embProg (Fin.castAdd 5) id (localBody f))) := by
  intro T place bank slots saved outgoing recursive body
  constructor <;> intro f <;> apply renamePlaced

private theorem recursiveChartTable_exec {T Q : ℕ} {P R U : Type}
    (chart : P → Pr P T Q prime U) (recursive : R → Pr (P ⊕ R) T Q prime U)
    {p s n t} (run : Exec chart p s n t) :
    Exec (recursiveChartTable chart recursive) (stateMapProg id id Sum.inl p) s n t :=
  stateMap_exec id id (fun _ => rfl) Sum.inl (fun _ => rfl) run

private theorem cutoffBudget_le {w width L V : ℕ} {recursive leaf : ℝ} (test : Prop) [Decidable test]
    (clock : w ≤ width) (size : width ≤ V) (positive : 0 < V) :
    ((4*w+23*width+22*L+51 : ℕ) : ℝ)+(if test then recursive+2 else leaf) ≤
      ((80*V+22*L : ℕ) : ℝ)+(if test then recursive else leaf) := by
  have bound : ((4*w+23*width+22*L+51 : ℕ) : ℝ)+2 ≤ ((80*V+22*L : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 4*w+23*width+22*L+51+2 ≤ 80*V+22*L)
  split_ifs <;> linarith

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- The root's binary precision simultaneously fits the cutoff and every
scheduled descendant width, and is at most the cutoff at every active level. -/
theorem scheduledChartPrecision (root : Descriptor) (depth b cutoff : ℕ)
    (levels : 0 < depth) (base : 0 < b) (width : root.width = 64^depth*b)
    (stop : 42^depth*b ≤ cutoff) (within : cutoff ≤ root.width)
    (path : List (Fin nodeChildren5.length)) (i : Fin nodeChildren5.length) :
    let L := root.width.size
    let node := path.foldl (scheduledChild prime) root
    cutoff < 2^L ∧ (scheduledChild prime node i).width.size ≤ L ∧ L ≤ cutoff := by
  intro L node
  have inherited := directoryDigits_bound prime root (path ++ [i])
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil] at inherited
  have budget := alignedRootWidth_le root depth b cutoff levels base width stop
  have pos : 0 < root.width := width ▸ Nat.mul_pos (pow_pos (by decide) _) base
  exact ⟨within.trans_lt (Nat.lt_size_self _),Nat.size_le_size (by dsimp only [node]; omega),
    Nat.size_le.mpr (by omega)⟩

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Initialize the saved cutoff at the root. Its single padded copy suffices
for every scheduled descent; the next selector reads exactly this tape. -/
theorem initializeChartCutoff_exec [M8.Machine.Net] {P U : Type} (K : ℕ)
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ ((K+1)+3+LeafCore.small)+1)
    (root : Descriptor) (depth b cutoff : ℕ) (levels : 0 < depth) (base : 0 < b)
    (width : root.width = 64^depth*b) (stop : 42^depth*b ≤ cutoff) (within : cutoff ≤ root.width) :
    let T := LeafCore.small
    let tapes := 66+(((K+1)+3+T)+1)
    let replay := directoryChartReplayBank room
    let cmp := chartCutoffBank K T ((by decide : 8 ≤ 9).trans nine_le_leaf) replay
    let L := root.width.size
    ∀ (body : P → Pr P ((tapes+10)+5) columnCapacity prime U) (src header : Fin ((tapes+10)+5))
      (u : HS ((tapes+10)+5) columnCapacity prime U) (S : Stacks ((tapes+10)+5) prime),
      [src,header,cmp 1,cmp 2,cmp 3,cmp 4].Nodup →
      S.R src = binSyms cutoff.size cutoff → S.R header = (Routines.hdr root 3).map bitSymbol →
      S.R (cmp 1) = [] → (∀ j, S.R (replay (stoppedChartPrivate (K+1) T j)) = []) →
      ∃ z, z.user = u.user ∧ Exec body ((bcopy src (cmp 1) (cmp 2) (cmp 3)).seq
        (bwiden (cmp 1) header (cmp 2) (cmp 3) (cmp 4))) (mk u S) (6*cutoff.size+12*L+24)
        (mk z {S with R := Function.update S.R (cmp 1) (binSyms L cutoff)}) ∧
        ∀ (path : List (Fin nodeChildren5.length)) (i : Fin nodeChildren5.length),
          cutoff < 2^L ∧ (scheduledChild prime (path.foldl (scheduledChild prime) root) i).width.size ≤ L ∧ L ≤ cutoff := by
  intro T tapes replay cmp L body src header u S regs word rootHeader fresh empty
  have precision : (S.R header).length = L := by
    rw [rootHeader]
    change ((FlatCoordinateSchedule.bits root.width).map (bitSymbol (a := prime))).length = root.width.size
    rw [canonicalBits_symbols,length_binSyms]
  have free (j : Fin 10) (hj : 2 ≤ j.val) : S.R (cmp j) = [] := by
    change S.R (chartCutoffBank K T _ replay j) = []
    rw [chartCutoffBank_scratch K T _ replay j hj]
    exact empty _
  obtain ⟨z,user,run⟩ := copyCutoff_exec body src header (cmp 1) (cmp 2) (cmp 3) (cmp 4) cutoff L
    (Nat.size_le_size within) u S regs word precision fresh (free 2 (by decide)) (free 3 (by decide)) (free 4 (by decide))
  exact ⟨z,user,run,scheduledChartPrecision root depth b cutoff levels base width stop within⟩

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- A physical batch on the active branch meets the next chart's width, row,
label-block and archive-size requirements. Only the spectator grouping differs
from the descriptor on the scheduled path. -/
theorem activeBatchChartDimensions (root node : Descriptor) (depth b cutoff blocks : ℕ)
    (levels : 0 < depth) (base : 0 < b) (rootWidth : root.width = 64^depth*b)
    (rootRows : 142080^depth ∣ root.rows) (stop : 42^depth*b ≤ cutoff)
    (path : List (Fin nodeChildren5.length)) (i : Fin nodeChildren5.length) (w : ℕ)
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) (positive : 0 < volume prime node)
    (pathWidth : (path.foldl (scheduledChild prime) root).width = node.width)
    (pathRows : (path.foldl (scheduledChild prime) root).rows = node.rows)
    (labels : node.beforeH = blocks*prime^(64*node.width)) :
    let r := nodeChildren5[i.val]
    let batch := ordinaryDirectoryChild (role node 142080) r (64-r) w
    let next := path++[i]
    let childClock := batch.width/64-1
    let childRows := batch.rows/142080
    let childBlocks := blocks*prime^(64*(node.width-batch.width))
    cutoff < batch.width →
    batch.Positive ∧ (next.foldl (scheduledChild prime) root).width = batch.width ∧
      (next.foldl (scheduledChild prime) root).rows = batch.rows ∧
      directoryDigits prime root next ≤ prime^batch.width ∧
      directoryDigits prime root path+(w+1)*(64*64) ≤ volume prime batch ∧
      batch.width = 64*(childClock+1) ∧ batch.rows = 142080*childRows ∧
        batch.beforeH = childBlocks*prime^(64*((childClock+1)*64)) ∧
        LabelMask.records (role node 142080) =
          (batch.beforeRows*childRows*childBlocks)*(142080*prime^(64*batch.width)) := by
  intro r batch next childClock childRows childBlocks active
  have shape := (scheduledDirectoryTranspose node i w aligned rows).1
  have pathW : (next.foldl (scheduledChild prime) root).width = batch.width := by
    rw [shape.width]
    simp only [next,List.foldl_append,List.foldl_cons,List.foldl_nil,scheduledChild,rankDescriptor,pathWidth]
  have pathR : (next.foldl (scheduledChild prime) root).rows = batch.rows := by
    rw [shape.rows]
    simp only [next,List.foldl_append,List.foldl_cons,List.foldl_nil,scheduledChild,rankDescriptor,role,pathRows]
  have pos := Nat.pos_of_mul_pos_right ((scheduledChild_measures prime node ⟨w+1,aligned⟩ rows i).2.symm ▸ positive)
  have budget : root.width*42^depth ≤ cutoff*64^depth := by
    rw [rootWidth]
    calc
      _ = (42^depth*b)*64^depth := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ stop
  have internal := scheduledPath_internal_alignment prime root depth cutoff ⟨b,rootWidth⟩ rootRows budget next
    (pathW.symm ▸ active)
  dsimp only at internal
  rw [pathW,pathR] at internal
  have fits := directoryDigits_fit_aligned prime Shared50ModularControl.prime_prime.two_le root depth b cutoff
    levels base rootWidth stop next (pathW.symm ▸ active.le)
  obtain ⟨d,hd⟩ := internal.1
  obtain ⟨n,hr⟩ := internal.2
  have dpos : 0 < d := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hd; omega
  have smaller : batch.width ≤ node.width := by
    change (w+1)*r ≤ node.width
    rw [aligned,Nat.mul_comm 64]
    exact Nat.mul_le_mul_left _ ((nodeChildren5_le i).trans (by decide : 42 ≤ 64))
  have rowCount : batch.rows = 142080*childRows := by dsimp only [childRows]; omega
  have clock : batch.width = 64*(childClock+1) := by dsimp only [childClock]; omega
  have rebuild : 64*(node.width-batch.width)+64*batch.width = 64*node.width := by omega
  have labelShape : batch.beforeH = childBlocks*prime^(64*batch.width) := by
    change node.beforeH = (blocks*prime^_)*prime^_
    rw [Nat.mul_assoc,← pow_add,rebuild,labels]
  have batchPos := LeafCore.positive_of_volume (shape.volume.symm ▸ pos)
  have prefixFits : directoryDigits prime root path+(w+1)*(64*64) ≤ volume prime batch := by
    have length : directoryDigits prime root next = directoryDigits prime root path+(w+1)*(64*64) := by
      rw [directoryDigits_append_call,pathWidth,aligned]
      simp
    rw [← length]
    apply (show directoryDigits prime root next ≤ prime^batch.width from pathW ▸ fits).trans
    obtain ⟨outer,rows,labels,between,afterD⟩ := batchPos
    have power := pow_pos Shared50ModularControl.prime_prime.pos batch.width
    unfold volume
    exact (((Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos outer rows) labels)).trans
      (Nat.le_mul_of_pos_right _ between)).trans (Nat.le_mul_of_pos_right _ power)).trans (Nat.le_mul_of_pos_right _ afterD)
  refine ⟨batchPos,pathW,pathR,pathW ▸ fits,prefixFits,
    clock,rowCount,?_,?_⟩
  · simpa only [← show (childClock+1)*64 = batch.width by omega] using labelShape
  · change batch.beforeRows*batch.rows*batch.beforeH = _
    rw [rowCount,labelShape]
    ring

/-- Fixed selector body for one interval rank. The width, cutoff and row
count are read at runtime. The large branch calls the supplied node label. -/
noncomputable def scheduledChartCall [M8.Machine.Net] (K : ℕ) {P R U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ ((K+1)+3+LeafCore.small)+1)
    (localBody : P → Pr P (66+((K+1)+3+LeafCore.small)) columnCapacity prime U)
    (rank : ℕ) (f : R) :
    Pr ((P ⊕ (P ⊕ Unit)) ⊕ R) ((66+(((K+1)+3+LeafCore.small)+1)+10)+5) columnCapacity prime U :=
  let T := LeafCore.small
  let replay := directoryChartReplayBank room
  let place := Fin.castLEEmb (show (66+(K+1))+3 ≤ 66+((K+1)+3+T) by omega)
  let prepare := IntervalDescriptor.directoryOuterHeaders (directoryOuterHeaderBank (K+1))
  let saved := fun j : Fin 3 => replay (stoppedChartHeader (K+1) T (j.castAdd 3))
  let release := (List.finRange 3).map saved
  let cmp := chartCutoffBank K T ((by decide : 8 ≤ 9).trans nine_le_leaf) replay
  let counts := (directoryChildCountBank (K+1) T ((by decide : 6 ≤ 9).trans nine_le_leaf)).trans replay
  let host := directoryChartHost room localBody (stoppedChartChild (K+1))
  let leaf := ((embProg replay Empty.elim (embProg place Empty.elim prepare)).seq (host (.inr (.inr ())))).seq
    (Prog.seqList (release.map WordCmd.dropR))
  let large := ((embProg replay Empty.elim (embProg place Empty.elim prepare)).seq
    (((prepareChildCounts counts).seq (.call (.inr f))).seq (Prog.seqList ([counts 2,counts 3].map WordCmd.dropR)))).seq
      (Prog.seqList (release.map WordCmd.dropR))
  (ordinaryCutoffTest cmp rank).seq (.cond (fun z => symBit (z.scan (cmp 7))) large (stateMapProg id id Sum.inl leaf))

/-- The generated scanner calls a rank selector by label. Each selector
can enter the same node procedure on the prepared child tapes. -/
noncomputable def scheduledChartProcedures [M8.Machine.Net] (K : ℕ) {P R U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ ((K+1)+3+LeafCore.small)+1)
    (localBody : P → Pr P (66+((K+1)+3+LeafCore.small)) columnCapacity prime U)
    (node : R → Pr ((P ⊕ (P ⊕ Unit)) ⊕ (Fin 43 ⊕ R))
      ((66+(((K+1)+3+LeafCore.small)+1)+10)+5) columnCapacity prime U) (f : R) :
    Fin 43 ⊕ R → Pr ((P ⊕ (P ⊕ Unit)) ⊕ (Fin 43 ⊕ R))
      ((66+(((K+1)+3+LeafCore.small)+1)+10)+5) columnCapacity prime U
  | .inl r => scheduledChartCall K room localBody r.val (.inr f)
  | .inr g =>
    let prefixPorts := (childPrefixPorts.trans (Fin.castAddEmb ((K+1)+3+LeafCore.small))).trans (directoryChartReplayBank room)
    withReplayPrefix prefixPorts (node g)

private theorem directorySelectorInputs {K T m w W H J : ℕ} {row : RecursiveInterchangeLayout.Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {weights : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {archiveTail : List (Fin (prime+4))}
    {schedule : List ℕ → List (Fin (prime+4))} {pending : List ℕ} {D : Stacks (66+(K+3+T)) prime}
    (ready : DirectoryReady row proj w W H J weights prefixes archiveTail schedule D pending) :
    let place := Fin.castLEEmb (show (66+K)+3 ≤ 66+(K+3+T) by omega)
    (∀ j : Fin 12, 3 ≤ j.val → D.R (place (directoryOuterHeaderBank K j)) = []) ∧
    (∀ j : Fin 3, D.R (stoppedChartHeader K T (j.natAdd 3)) = (Routines.hdr row (j.natAdd 3)).map bitSymbol) ∧
    (∀ j, D.L (stoppedChartPrivate K T j) = [] ∧ D.R (stoppedChartPrivate K T j) = []) ∧
    (D.R ((45 : Fin 66).castAdd (K+3+T))).length = w := by
  intro place
  obtain ⟨_,_,work,_,_,_,_,_,headers,_,clock,_,_⟩ := ready
  refine ⟨?_,?_,?_,clock⟩
  · intro j high
    apply (work _ _).2
    change 58 ≤ if j.val < 3 then _ else if j.val < 6 then _ else _
    split_ifs <;> omega
  · intro j
    have idx : stoppedChartHeader K T (j.natAdd 3) =
        (((j.natAdd 3).natAdd 33).castLE (by decide : 39 ≤ 66)).castAdd (K+3+T) := by
      apply Fin.ext
      simp [stoppedChartHeader,Fin.natAdd]
    rw [idx]
    exact headers (j.natAdd 3)
  · intro j
    apply work
    change 58 ≤ 66+K+3+j.val
    omega

open RecursiveInterchangeLayout in
noncomputable def scheduledLeafCost (scheduled : Descriptor) : ℝ :=
  let T := LeafCore.small
  ((223+((T+5 : ℕ)*|LeafCore.C|+8+T*(16+8*|LeafCore.C|)))*scheduled.width)*volume prime scheduled

open RecursiveInterchangeLayout in
noncomputable def scheduledBranchCost (scheduled : Descriptor) (cutoff recursiveBudget : ℕ) : ℝ :=
  if cutoff < scheduled.width then (recursiveBudget : ℝ) else scheduledLeafCost scheduled

open RecursiveInterchangeLayout in
/-- The packed scanner requests an integral budget before calling its child. -/
noncomputable def scheduledChartBudget (scheduled : Descriptor) (cutoff recursiveBudget : ℕ) : ℕ :=
  ⌊((1710*volume prime scheduled : ℕ) : ℝ)+scheduledBranchCost scheduled cutoff recursiveBudget⌋₊

/-- Decoding the two child counts and saving the three outer headers preserves
all public scanner words, including the inherited directory and its prefixPorts width. -/
private theorem childCountState_public {n K T : ℕ} (room : 6 ≤ T)
    (replay : Fin (66+(K+3+T)) ↪ Fin n) (batch : RecursiveInterchangeLayout.Descriptor)
    (A F : Stacks n prime)
    (keep : ∀ j, (∀ i : Fin 3, j ≠ replay (stoppedChartHeader K T (i.castAdd 3))) →
      F.L j = A.L j ∧ F.R j = A.R j) (i : Fin 66) :
    let port := replay (i.castAdd (K+3+T))
    let counts := (directoryChildCountBank K T room).trans replay
    (childCountState counts batch F).R port = A.R port := by
  intro port counts
  have off (j : Fin 8) (high : 2 ≤ j.val) : port ≠ counts j := by
    apply replay.injective.ne
    intro eq
    have h := congrArg Fin.val eq
    change i.val = (if j.val = 0 then 36 else if j.val = 1 then _ else _) at h
    split_ifs at h <;> omega
  simp only [childCountState,Function.update_of_ne (off 3 (by decide)),Function.update_of_ne (off 2 (by decide))]
  apply (keep port _).2
  intro j
  apply replay.injective.ne
  intro eq
  have h := congrArg Fin.val eq
  change i.val = (if j.val < 3 then _ else _) at h
  split_ifs at h <;> omega

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Read the parent's cutoff and execute the selected batch branch. In the
recursive case the continuation receives a proof of strict width descent. -/
theorem selectScheduledChart_exec [M8.Machine.Net] (K : ℕ) {P R U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ ((K+1)+3+LeafCore.small)+1)
    (localBody : P → Pr P (66+((K+1)+3+LeafCore.small)) columnCapacity prime U)
    (node : Descriptor) (i : Fin nodeChildren5.length) (lo hi w L cutoff : ℕ)
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) (rank : hi-lo = nodeChildren5[i.val]) :
    let parent := role node 142080
    let batch := ordinaryDirectoryChild parent nodeChildren5[i.val] (64-nodeChildren5[i.val]) w
    let row := remainderRecordChild lo hi (w+1) (parent.between*parent.afterD)
    let scheduled := scheduledChild prime node i
    let T := LeafCore.small
    let tapes := 66+(((K+1)+3+T)+1)
    let owner := (0 : Fin 5).natAdd (tapes+10)
    let host := directoryChartHost room localBody (stoppedChartChild (K+1))
    let replay := directoryChartReplayBank room
    let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
    let saved := fun j : Fin 3 => replay (stoppedChartHeader (K+1) T (j.castAdd 3))
    let leafBudget := ((223+((T+5 : ℕ)*|LeafCore.C|+8+T*(16+8*|LeafCore.C|)))*scheduled.width)*volume prime scheduled
    ∀ (recursive : R → Pr ((P ⊕ (P ⊕ Unit)) ⊕ (Fin 43 ⊕ R)) ((tapes+10)+5) columnCapacity prime U) (f : R) (recursiveBudget : ℕ),
    let procedures := scheduledChartProcedures K room localBody recursive f
    let body := recursiveChartTable host procedures
    let counts := (directoryChildCountBank (K+1) T (show 6 ≤ T from (by decide : 6 ≤ 9).trans nine_le_leaf)).trans replay
    let prefixPorts := (childPrefixPorts.trans (Fin.castAddEmb ((K+1)+3+T))).trans replay
    ∀ (a : HS ((tapes+10)+5) columnCapacity prime U) (A : Stacks ((tapes+10)+5) prime)
      (x : Fin (volume prime batch) → ZMod 2), 0 < volume prime node →
      (∀ j : Fin 3, (directoryOuterWords (embStk replay A) j).length = values j) →
      ∀ {W H J : ℕ} {proj : Matrix (Fin 64) (Fin 64) ℚ} {weights : Fin 64 → ZMod (prime^(w+1))}
        {prefixes : ℕ → List (Fin (prime+4))} {pending : List ℕ},
      DirectoryReady row proj w W H J weights prefixes [] (fun _ => []) (embStk replay A) pending →
      RecordPayload owner (fun _ => blank) 0 x A →
      cutoff < node.width → (cutoff < 2^L ∧ scheduled.width.size ≤ L ∧ L ≤ cutoff) →
      A.R (replay ((40 : Fin 66).castAdd ((K+1)+3+T))) = binSyms L cutoff →
      (cutoff < batch.width → (A.R (prefixPorts 0)).length+(w+1)*(64*64) ≤ volume prime batch) →
      (cutoff < batch.width → batch.width < node.width → batch.Positive →
        ∀ (z : HS ((tapes+10)+5) columnCapacity prime U) (F : Stacks ((tapes+10)+5) prime),
        let D := childCountState counts batch F
        let next := (D.R (prefixPorts 0)).length+(w+1)*(64*64)
        let E := {D with R := Function.update D.R (prefixPorts 3) (List.replicate next Node.tick)}
        StoppedChartReady (K+1) T batch (embStk replay F) →
        (∀ j, (∀ l : Fin 3, j ≠ saved l) → F.L j = A.L j ∧ F.R j = A.R j) →
        (∀ j : Fin 66, D.R (replay (j.castAdd ((K+1)+3+T))) = A.R (replay (j.castAdd ((K+1)+3+T)))) →
        E.R (replay ((46 : Fin 66).castAdd ((K+1)+3+T))) = pending.flatMap (LabelDirectory.entry prefixes 64 (w+1)) →
        (∀ j ∈ pending, (LabelDirectory.entry prefixes 64 (w+1) j).length = (E.R (prefixPorts 3)).length) →
        RecordPayload owner (fun _ => blank) 0 x E →
        ∃ y B, ∃ k : ℕ, y.user = z.user ∧ k ≤ recursiveBudget ∧
          Exec body (recursive f) (mk z E) k (mk y B) ∧
          RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
          ∀ j, j ≠ owner → B.L j = E.L j ∧ B.R j = E.R j) →
      ∃ y B, ∃ k : ℕ, y.user = a.user ∧ k ≤ ⌊((1710*volume prime scheduled : ℕ) : ℝ)+
        (if cutoff < scheduled.width then (recursiveBudget : ℝ) else leafBudget)⌋₊ ∧
        Exec body (body (.inr (.inl ⟨hi-lo,by have := nodeChildren5_le i; omega⟩)))
          (mk a A) k (mk y B) ∧
        RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
        ∀ j, j ≠ owner → B.L j = A.L j ∧ B.R j = A.R j := by
  intro parent batch row scheduled T tapes owner host replay values saved leafBudget
    recursive f recursiveBudget procedures body counts prefixPorts a A x positive src W H J proj weights prefixes pending directoryReady
    payload activeParent ⟨cutFits,fits,precision⟩ cutWord prefixFits recurse
  let place := Fin.castLEEmb (show (66+(K+1))+3 ≤ 66+((K+1)+3+T) by omega)
  let bank := directoryOuterHeaderBank (K+1)
  let cmp := chartCutoffBank K T ((by decide : 8 ≤ 9).trans nine_le_leaf) replay
  obtain ⟨empty,tail,free,clock⟩ := directorySelectorInputs (K := K+1) (T := T) directoryReady
  change ∀ j : Fin 12, 3 ≤ j.val → A.R (replay (place (bank j))) = [] at empty
  change ∀ j : Fin 3, A.R (replay (stoppedChartHeader (K+1) T (j.natAdd 3))) =
    (Routines.hdr row (j.natAdd 3)).map bitSymbol at tail
  change ∀ j, A.L (replay (stoppedChartPrivate (K+1) T j)) = [] ∧
    A.R (replay (stoppedChartPrivate (K+1) T j)) = [] at free
  change (A.R (cmp 0)).length = w at clock
  have sources (j : Fin 3) : (A.R (replay (place (bank (j.castAdd 9))))).length = values j := by
    have index : place (bank (j.castAdd 9)) = ((j.natAdd 29).castLE (by decide : 32 ≤ 66)).castAdd ((K+1)+3+T) := by
      apply Fin.ext
      change (if j.val < 3 then _ else _) = _
      rw [ite_eq_left j.isLt]
      rfl
    rw [index]
    exact src j
  let scratch := (List.finRange 3).map saved
  let leaf := ((embProg replay Empty.elim (embProg place Empty.elim (IntervalDescriptor.directoryOuterHeaders bank))).seq
      (host (.inr (.inr ())))).seq (Prog.seqList (scratch.map WordCmd.dropR))
  let large : Pr ((P ⊕ (P ⊕ Unit)) ⊕ (Fin 43 ⊕ R)) ((tapes+10)+5) columnCapacity prime U :=
      (((embProg replay Empty.elim (embProg place Empty.elim (IntervalDescriptor.directoryOuterHeaders bank))).seq
        (((prepareChildCounts counts).seq (.call (.inr (.inr f)))).seq (Prog.seqList ([counts 2,counts 3].map WordCmd.dropR)))).seq (Prog.seqList (scratch.map WordCmd.dropR)))
  have shape := (scheduledDirectoryTranspose node i w aligned rows).1
  have width : (w+1)*(hi-lo) = scheduled.width := by
    rw [rank]
    exact shape.width
  have run := chartCutoff_exec body cmp (hi-lo) w L cutoff cutFits (width.symm ▸ fits) large (stateMapProg id id Sum.inl leaf) a A clock cutWord
    (fun j hj => by
      change A.R (chartCutoffBank K T _ replay j) = []
      rw [chartCutoffBank_scratch K T _ replay j hj]
      exact (free _).2)
    (fun B => RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
      ∀ j, j ≠ owner → B.L j = A.L j ∧ B.R j = A.R j)
    (if cutoff < scheduled.width then (recursiveBudget : ℝ)+(222*volume prime scheduled : ℕ)+2 else leafBudget)
  rw [width] at run
  have charge := (scheduledChild_measures prime node ⟨w+1,aligned⟩ rows i).2
  have pos : 0 < volume prime scheduled := Nat.pos_of_mul_pos_right (charge.symm ▸ positive)
  have size : scheduled.width ≤ volume prime scheduled :=
    RecursiveHeaderBounds.values_le_volume Shared50ModularControl.prime_prime.two_le scheduled (LeafCore.positive_of_volume pos) 3
  have atomBound : w+1 ≤ scheduled.width := by
    rw [← width]
    exact Nat.le_mul_of_pos_right _ (rank.symm ▸ (nodeChildren5_bounds i).1)
  obtain ⟨y,B,k,user,paid,execution,out,frame⟩ := run (fun z => by
    by_cases active : cutoff < scheduled.width
    · simp only [ite_eq_left active]
      have smaller : scheduled.width < node.width := by
        have bound := (nodeChildren5_bounds i).2
        rw [← width,rank,aligned,Nat.mul_comm 64]
        exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.succ_pos _)
      have batchSize : volume prime batch = volume prime scheduled := shape.volume
      have batchWidth : batch.width = scheduled.width := shape.width
      have batchPos := LeafCore.positive_of_volume (batchSize.symm ▸ pos)
      have hp := RecursiveRowsNodeLayout.role_positive 142080 node (by decide) (LeafCore.positive_of_volume positive) rows
      have apart (j) : replay j ≠ owner := by
        have sep := directoryReplay_owner_ne (directoryOrdinaryBank room) (directoryChartPlacement tapes)
          (replaySlots.trans (Fin.castAddEmb ((K+1)+3+T))) ((Fin.castLEEmb (by decide : 4 ≤ 6)).trans (directoryChartReplay tapes))
          (fun i j => directoryChartPlacement_ne_work i _) j (0 : Fin 5)
        rw [directoryChartPlacement_owner] at sep
        exact sep
      let core : Pr ((P ⊕ (P ⊕ Unit)) ⊕ (Fin 43 ⊕ R)) ((tapes+10)+5) columnCapacity prime U :=
        ((prepareChildCounts counts).seq (.call (.inr (.inr f)))).seq (Prog.seqList ([counts 2,counts 3].map WordCmd.dropR))
      have prepared := withDirectoryHeaders_exec body replay owner apart core parent hp lo hi w
        ((recursiveBudget+28*volume prime batch+2)+81*volume prime batch) z A
      rw [rank] at prepared
      have call := recurse (batchWidth.symm ▸ active) (batchWidth.symm ▸ smaller) batchPos
      obtain ⟨y,B,k,user,paid,execution,out,frame⟩ := prepared x sources empty tail free payload (by
        intro v F ready keep input
        have registers := directoryChildCountBank_ready (K := K+1) (T := T) ((by decide : 6 ≤ 9).trans nine_le_leaf)
          replay batch F ready
        apply withChildCounts_exec body counts owner (fun j => apart _) batch (batchSize.symm ▸ pos) (.call (.inr (.inr f)))
          (recursiveBudget+28*volume prime batch+2) v F _ registers.1 registers.2.1 registers.2.2
        intro v'
        have childInput : RecordPayload owner (fun _ => blank) 0 x (childCountState counts batch F) := by
          intro t
          have ne₂ : owner ≠ counts 2 := (apart _).symm
          have ne₃ : owner ≠ counts 3 := (apart _).symm
          simpa only [childCountState, Function.update_of_ne ne₃, Function.update_of_ne ne₂] using input t
        have publicWords := childCountState_public ((by decide : 6 ≤ 9).trans nine_le_leaf) replay batch A F keep
        have fitsHere := prefixFits (batchWidth.symm ▸ active)
        have hclock := publicWords 47
        change (childCountState counts batch F).R (prefixPorts 0) = A.R (prefixPorts 0) at hclock
        obtain ⟨y,B,k,user,time,run,out,frame⟩ := withReplayPrefix_exec body replay owner apart row proj weights prefixes
          pending v' (childCountState counts batch F) (embStk replay A) directoryReady publicWords (recursive f) recursiveBudget
          x (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) childInput
          (by change ((childCountState counts batch F).R (prefixPorts 0)).length+_ ≤ _; rwa [hclock])
          (fun z archive widths word => call z F ready keep publicWords archive widths word)
        exact ⟨y,B,k+2,user,Nat.add_le_add_right time 2,Exec.call run,out,frame⟩)
      obtain ⟨count,erase⟩ := directoryHeaderCosts parent nodeChildren5[i.val] (64-nodeChildren5[i.val]) w (batchSize.symm ▸ pos)
      have bound : k ≤ 222*volume prime scheduled + recursiveBudget+2 := by
        change LabelMask.records parent ≤ volume prime batch at count
        change _ ≤ 19*volume prime batch at erase
        rw [batchSize] at count erase paid
        omega
      refine ⟨y,B,k,user,?_,execution,out,frame⟩
      have realBound := (Nat.cast_le (α := ℝ)).mpr bound
      push_cast at realBound ⊢
      linarith
    · simp only [ite_eq_right active]
      have stopped := dispatchStoppedChart_exec (K+1) room localBody node i lo hi w aligned rows rank z A
      rw [rank] at stopped
      obtain ⟨y,B,k,user,paid,call,out,frame⟩ := stopped x positive sources empty tail free payload
      exact ⟨y,B,k,user,paid,recursiveChartTable_exec host procedures call,out,frame⟩)
  have comparison := cutoffBudget_le (cutoff < scheduled.width) ((Nat.le_succ w).trans atomBound) size pos
    (recursive := (recursiveBudget : ℝ)+(222*volume prime scheduled : ℕ)) (leaf := leafBudget) (L := L)
  have parentBound := Nat.mul_le_mul_left 64 (atomBound.trans size)
  have scaled : 80*volume prime scheduled+22*L+222*volume prime scheduled ≤ 1710*volume prime scheduled := by omega
  have cost := paid.trans comparison
  refine ⟨y,B,k,user,?_,execution,out,frame⟩
  apply Nat.le_floor
  have slack := (Nat.cast_le (α := ℝ)).mpr scaled
  have nonneg : (0 : ℝ) ≤ volume prime scheduled := Nat.cast_nonneg _
  split_ifs at cost ⊢ <;> push_cast at cost slack ⊢ <;> linarith


open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Sum the selector costs over the directory occurrences of a parent. Each
selected child budget is charged once, independently of its stopping decision. -/
theorem scheduledChartDispatch_sum (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (calls : Finset (Fin nodeChildren5.length)) (cutoff : ℕ) (recursiveBudget : Fin nodeChildren5.length → ℕ) :
    let child := scheduledChild prime node
    ∑ i ∈ calls, (scheduledChartBudget (child i) cutoff (recursiveBudget i) : ℝ) ≤
      (calls.card*1710/142080 : ℝ)*volume prime node + ∑ i ∈ calls, scheduledBranchCost (child i) cutoff (recursiveBudget i) := by
  intro child
  have paid (i) : (scheduledChartBudget (child i) cutoff (recursiveBudget i) : ℝ) ≤
      ((1710*volume prime (child i) : ℕ) : ℝ)+scheduledBranchCost (child i) cutoff (recursiveBudget i) := by
    apply Nat.floor_le
    unfold scheduledBranchCost scheduledLeafCost
    split_ifs <;> positivity
  have share (i : Fin nodeChildren5.length) : (volume prime (scheduledChild prime node i) : ℝ)*142080 = volume prime node := by
    exact_mod_cast (scheduledChild_measures prime node width rows i).2
  have price (i) : ((1710*volume prime (scheduledChild prime node i) : ℕ) : ℝ) =
      (1710/142080 : ℝ)*volume prime node := by
    rw [← share i]
    push_cast
    ring
  calc
    _ ≤ ∑ i ∈ calls, (((1710*volume prime (scheduledChild prime node i) : ℕ) : ℝ)+scheduledBranchCost (child i) cutoff (recursiveBudget i)) := Finset.sum_le_sum (fun i _ => paid i)
    _ = _ := by simp only [price,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]; ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
