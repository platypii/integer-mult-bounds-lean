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

/-- Test the width using the scanner's predecessor clock on tape 45 and the
cutoff saved immediately before the outer headers. The eight scratch tapes
belong to the leaf and are restored before either continuation starts. -/
def chartCutoffBank (K T : ℕ) (room : 8 ≤ T) : Fin 10 ↪ Fin (66+((K+1)+3+T)) where
  toFun j := ⟨if j.val = 0 then 45 else if j.val = 1 then 66+K else 66+(K+1)+3+(j.val-2),
    by split_ifs <;> omega⟩
  inj' := by
    intro j l eq
    apply Fin.ext
    have h := congrArg Fin.val eq
    dsimp only at h
    split_ifs at h <;> omega

private theorem chartCutoffBank_scratch (K T : ℕ) (room : 8 ≤ T) (j : Fin 10) (high : 2 ≤ j.val) :
    chartCutoffBank K T room j = stoppedChartPrivate (K+1) T ⟨j.val-2,by omega⟩ := by
  apply Fin.ext
  change (if j.val = 0 then 45 else if j.val = 1 then 66+K else 66+(K+1)+3+(j.val-2)) = 66+(K+1)+3+(j.val-2)
  split_ifs <;> omega

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
    let cmp := (chartCutoffBank K T (show 8 ≤ T from (by decide : 8 ≤ 9).trans nine_le_leaf)).trans replay
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
    change S.R (replay (chartCutoffBank K T _ j)) = []
    rw [chartCutoffBank_scratch K T _ j hj]
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
  refine ⟨LeafCore.positive_of_volume (shape.volume.symm ▸ pos),pathW,pathR,pathW ▸ fits,
    clock,rowCount,?_,?_⟩
  · simpa only [← show (childClock+1)*64 = batch.width by omega] using labelShape
  · change batch.beforeRows*batch.rows*batch.beforeH = _
    rw [rowCount,labelShape]
    ring

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
    let place := Fin.castLEEmb (show (66+(K+1))+3 ≤ 66+((K+1)+3+T) by omega)
    let bank := directoryOuterHeaderBank (K+1)
    let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
    let saved := fun j : Fin 3 => replay (stoppedChartHeader (K+1) T (j.castAdd 3))
    let scratch := (List.finRange 3).map saved
    let cmp := (chartCutoffBank K T (show 8 ≤ T from (by decide : 8 ≤ 9).trans nine_le_leaf)).trans replay
    let leaf := ((embProg replay Empty.elim (embProg place Empty.elim (IntervalDescriptor.directoryOuterHeaders bank))).seq
      (host (.inr (.inr ())))).seq (Prog.seqList (scratch.map WordCmd.dropR))
    let leafBudget := ((223+((T+5 : ℕ)*|LeafCore.C|+8+T*(16+8*|LeafCore.C|)))*scheduled.width)*volume prime scheduled
    ∀ (recursive : R → Pr ((P ⊕ (P ⊕ Unit)) ⊕ R) ((tapes+10)+5) columnCapacity prime U) (f : R) (recursiveBudget : ℕ),
    let body := recursiveChartTable host recursive
    let counts := (directoryChildCountBank (K+1) T (show 6 ≤ T from (by decide : 6 ≤ 9).trans nine_le_leaf)).trans replay
    let large : Pr ((P ⊕ (P ⊕ Unit)) ⊕ R) ((tapes+10)+5) columnCapacity prime U :=
      (((embProg replay Empty.elim (embProg place Empty.elim (IntervalDescriptor.directoryOuterHeaders bank))).seq
        (((prepareChildCounts counts).seq (.call (.inr f))).seq (Prog.seqList ([counts 2,counts 3].map WordCmd.dropR)))).seq (Prog.seqList (scratch.map WordCmd.dropR)))
    ∀ (a : HS ((tapes+10)+5) columnCapacity prime U) (A : Stacks ((tapes+10)+5) prime)
      (x : Fin (volume prime batch) → ZMod 2), 0 < volume prime node →
      (∀ j : Fin 3, (A.R (replay (place (bank (j.castAdd 9))))).length = values j) →
      (∀ j : Fin 12, 3 ≤ j.val → A.R (replay (place (bank j))) = []) →
      (∀ j : Fin 3, A.R (replay (stoppedChartHeader (K+1) T (j.natAdd 3))) = (Routines.hdr row (j.natAdd 3)).map bitSymbol) →
      (∀ j, A.L (replay (stoppedChartPrivate (K+1) T j)) = [] ∧ A.R (replay (stoppedChartPrivate (K+1) T j)) = []) →
      RecordPayload owner (fun _ => blank) 0 x A →
      cutoff < node.width → (cutoff < 2^L ∧ scheduled.width.size ≤ L ∧ L ≤ cutoff) →
      (A.R (cmp 0)).length = w → A.R (cmp 1) = binSyms L cutoff →
      (cutoff < batch.width → batch.width < node.width → batch.Positive →
        ∀ (z : HS ((tapes+10)+5) columnCapacity prime U) (F : Stacks ((tapes+10)+5) prime),
        let D := childCountState counts batch F
        StoppedChartReady (K+1) T batch (embStk replay F) →
        (∀ j, (∀ l : Fin 3, j ≠ saved l) → F.L j = A.L j ∧ F.R j = A.R j) →
        RecordPayload owner (fun _ => blank) 0 x D →
        ∃ y B, ∃ k : ℕ, y.user = z.user ∧ (k : ℝ) ≤ recursiveBudget ∧
          Exec body (recursive f) (mk z D) k (mk y B) ∧
          RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
          ∀ j, j ≠ owner → B.L j = D.L j ∧ B.R j = D.R j) →
      ∃ y B, ∃ k : ℕ, y.user = a.user ∧ (k : ℝ) ≤ (1682*volume prime scheduled : ℕ)+
        (if cutoff < scheduled.width then (recursiveBudget : ℝ) else leafBudget) ∧
        Exec body ((ordinaryCutoffTest cmp (hi-lo)).seq (.cond (fun z => symBit (z.scan (cmp 7))) large
          (stateMapProg id id Sum.inl leaf)))
          (mk a A) k (mk y B) ∧
        RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
        ∀ j, j ≠ owner → B.L j = A.L j ∧ B.R j = A.R j := by
  intro parent batch row scheduled T tapes owner host replay place bank values saved scratch cmp leaf leafBudget
    recursive f recursiveBudget body counts large a A x positive src empty tail free payload activeParent ⟨cutFits,fits,precision⟩ clock cutWord recurse
  have shape := (scheduledDirectoryTranspose node i w aligned rows).1
  have width : (w+1)*(hi-lo) = scheduled.width := by
    rw [rank]
    exact shape.width
  have run := chartCutoff_exec body cmp (hi-lo) w L cutoff cutFits (width.symm ▸ fits) large (stateMapProg id id Sum.inl leaf) a A clock cutWord
    (fun j hj => by
      change A.R (replay (chartCutoffBank K T _ j)) = []
      rw [chartCutoffBank_scratch K T _ j hj]
      exact (free _).2)
    (fun B => RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) B ∧
      ∀ j, j ≠ owner → B.L j = A.L j ∧ B.R j = A.R j)
    (if cutoff < scheduled.width then (recursiveBudget : ℝ)+(194*volume prime scheduled : ℕ)+2 else leafBudget)
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
      let core : Pr ((P ⊕ (P ⊕ Unit)) ⊕ R) ((tapes+10)+5) columnCapacity prime U :=
        ((prepareChildCounts counts).seq (.call (.inr f))).seq (Prog.seqList ([counts 2,counts 3].map WordCmd.dropR))
      have prepared := withDirectoryHeaders_exec body replay owner apart core parent hp lo hi w
        ((recursiveBudget+2)+81*volume prime batch) z A
      rw [rank] at prepared
      have call := recurse (batchWidth.symm ▸ active) (batchWidth.symm ▸ smaller) batchPos
      obtain ⟨y,B,k,user,paid,execution,out,frame⟩ := prepared x src empty tail free payload (by
        intro v F ready keep input
        have registers := directoryChildCountBank_ready (K := K+1) (T := T) ((by decide : 6 ≤ 9).trans nine_le_leaf)
          replay batch F ready
        apply withChildCounts_exec body counts owner (fun j => apart _) batch (batchSize.symm ▸ pos) (.call (.inr f))
          (recursiveBudget+2) v F _ registers.1 registers.2.1 registers.2.2
        intro v'
        have childInput : RecordPayload owner (fun _ => blank) 0 x (childCountState counts batch F) := by
          intro t
          have ne₂ : owner ≠ counts 2 := (apart _).symm
          have ne₃ : owner ≠ counts 3 := (apart _).symm
          simpa only [childCountState, Function.update_of_ne ne₃, Function.update_of_ne ne₂] using input t
        obtain ⟨y,B,k,user,time,run,out,frame⟩ := call v' F ready keep childInput
        exact ⟨y,B,k+2,user,Nat.add_le_add_right ((Nat.cast_le (α := ℝ)).mp time) 2,Exec.call run,out,frame⟩)
      obtain ⟨count,erase⟩ := directoryHeaderCosts parent nodeChildren5[i.val] (64-nodeChildren5[i.val]) w (batchSize.symm ▸ pos)
      have bound : k ≤ 194*volume prime scheduled + recursiveBudget+2 := by
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
      obtain ⟨y,B,k,user,paid,call,out,frame⟩ := stopped x positive src empty tail free payload
      exact ⟨y,B,k,user,paid,recursiveChartTable_exec host recursive call,out,frame⟩)
  have comparison := cutoffBudget_le (cutoff < scheduled.width) ((Nat.le_succ w).trans atomBound) size pos
    (recursive := (recursiveBudget : ℝ)+(194*volume prime scheduled : ℕ)) (leaf := leafBudget) (L := L)
  have parentBound := Nat.mul_le_mul_left 64 (atomBound.trans size)
  have scaled : 80*volume prime scheduled+22*L+194*volume prime scheduled ≤ 1682*volume prime scheduled := by omega
  have cost := paid.trans comparison
  refine ⟨y,B,k,user,?_,execution,out,frame⟩
  have slack := (Nat.cast_le (α := ℝ)).mpr scaled
  have nonneg : (0 : ℝ) ≤ volume prime scheduled := Nat.cast_nonneg _
  split_ifs at cost ⊢ <;> push_cast at cost slack ⊢ <;> linarith


open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Sum the selector costs over the directory occurrences of a parent. Each
selected child budget is charged once, independently of its stopping decision. -/
theorem scheduledChartDispatch_sum (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (calls : Finset (Fin nodeChildren5.length)) (steps budget : Fin nodeChildren5.length → ℝ)
    (paid : ∀ i ∈ calls, steps i ≤ (1682*volume prime (scheduledChild prime node i) : ℕ)+budget i) :
    ∑ i ∈ calls, steps i ≤ (calls.card*1682/142080 : ℝ)*volume prime node + ∑ i ∈ calls, budget i := by
  have share (i : Fin nodeChildren5.length) : (volume prime (scheduledChild prime node i) : ℝ)*142080 = volume prime node := by
    exact_mod_cast (scheduledChild_measures prime node width rows i).2
  have price (i) : ((1682*volume prime (scheduledChild prime node i) : ℕ) : ℝ) =
      (1682/142080 : ℝ)*volume prime node := by
    rw [← share i]
    push_cast
    ring
  calc
    _ ≤ ∑ i ∈ calls, (((1682*volume prime (scheduledChild prime node i) : ℕ) : ℝ)+budget i) := Finset.sum_le_sum paid
    _ = _ := by simp only [price,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]; ring

end IntegerMultBounds.MathlibTM2.M6.BitNode
