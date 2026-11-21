module

public import IntegerMultBounds.MathlibTM2.Host.StateTransport
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryRoleChartEntry

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
          batch.beforeRows*childRows*142080*batch.beforeH := by
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
    rw [rowCount]
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

/-- The two factor headers are public. The ten work tapes follow the two
live child counts in the private leaf bank. -/
def directorySpectatorBank (K T : ℕ) (room : 12 ≤ T) : Fin 12 ↪ Fin (66+(K+3+T)) where
  toFun i := ⟨if i.val < 10 then 66+K+3+2+i.val else 27+i.val, by split <;> omega⟩
  inj' := by
    intro i j eq
    apply Fin.ext
    have h := congrArg Fin.val eq
    dsimp only at h
    split_ifs at h <;> omega

theorem modulusRoom [M8.Machine.Net] : 16 ≤ LeafCore.small := by
  simp only [LeafCore.small, M8.Machine.ArbitraryWidthOriginalZeroBranch.count,
    M8.Machine.ArbitraryWidthOriginalZeroBranch.highCount]
  omega

theorem spectatorRoom [M8.Machine.Net] : 12 ≤ LeafCore.small := (by decide : 12 ≤ 16).trans modulusRoom

noncomputable def withDirectorySpectator {T Q : ℕ} {P U : Type} (r : Fin 12 ↪ Fin T) (core : Pr P T Q prime U) :=
  ((directorySpectatorWord r).seq core).seq (Prog.seqList ([r 0,r 1,r 2,r 3].map WordCmd.dropR))

open RecursiveInterchangeLayout in
theorem withDirectorySpectator_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 12 ↪ Fin T) (owner : Fin T) (apart : ∀ i, r i ≠ owner)
    (batch : Descriptor) (hp : batch.Positive) (core : Pr P T Q prime U) (budget : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) (input word : Fin (volume prime batch) → ZMod 2)
    (payload : RecordPayload owner (fun _ => blank) 0 input S)
    (between : S.R (r 10) = (FlatCoordinateSchedule.bits batch.between).map bitSymbol)
    (afterD : S.R (r 11) = (FlatCoordinateSchedule.bits batch.afterD).map bitSymbol)
    (empty : ∀ i : Fin 10, S.R (r (i.castAdd 2)) = []) :
    let D := directorySpectatorState r batch.between batch.afterD S
    (∀ v : HS T Q prime U, RecordPayload owner (fun _ => blank) 0 input D → ∃ y B k, y.user = v.user ∧ k ≤ budget ∧ Exec body core (mk v D) k (mk y B) ∧
      RecordPayload owner (fun _ => blank) 0 word B ∧ ∀ j, j ≠ owner → B.L j = D.L j ∧ B.R j = D.R j) →
    ∃ z F k, z.user = u.user ∧ k ≤ budget+133*volume prime batch ∧
      Exec body (withDirectorySpectator r core) (mk u S) k (mk z F) ∧
      RecordPayload owner (fun _ => blank) 0 word F ∧ ∀ j, j ≠ owner → F.L j = S.L j ∧ F.R j = S.R j := by
  intro D child
  obtain ⟨v,n,user,paid,prep⟩ := directorySpectatorWord_exec body r u S _ _ hp.2.2.2.1 hp.2.2.2.2 between afterD empty
  obtain ⟨y,B,k,same,time,run,out,frame⟩ := child v (fun i => by
    simpa only [D,directorySpectatorState,Function.update_of_ne (apart 0).symm,Function.update_of_ne (apart 1).symm,
      Function.update_of_ne (apart 2).symm,Function.update_of_ne (apart 3).symm] using payload i)
  obtain ⟨z,F,last,erase,left,right⟩ := retire_exec body [r 0,r 1,r 2,r 3] (by simp) y B
  let W := batch.between*batch.afterD
  have lb : batch.between ≤ W := Nat.le_mul_of_pos_right _ hp.2.2.2.2
  have ld : batch.afterD ≤ W := Nat.le_mul_of_pos_left _ hp.2.2.2.1
  have bits : W.size ≤ W := Nat.size_le.mpr Nat.lt_two_pow_self
  have scale : W ≤ volume prime batch := by
    have h : 0 < batch.beforeRows*batch.rows*batch.beforeH*prime^batch.width*prime^batch.width :=
      by obtain ⟨_,_,_,_,_⟩ := hp; have := Shared50ModularControl.prime_prime.pos; positivity
    convert Nat.le_mul_of_pos_left W h using 1 <;> simp only [W,volume] <;> ring
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at erase
  have lengths (i : Fin 12) := congrArg List.length (frame _ (apart i)).2
  simp [lengths,D,directorySpectatorState,length_binSyms] at erase
  refine ⟨z,F,_,last.trans (same.trans user),?_,Exec.seq (Exec.seq prep run) erase,?_,?_⟩
  · change n ≤ 68*W+48 at paid
    have pos : 0 < W := Nat.mul_pos hp.2.2.2.1 hp.2.2.2.2
    dsimp only [W] at *
    omega
  · intro t
    rw [show F.L owner = B.L owner from congrFun left owner,right,ite_eq_right (by simp [(apart 0).symm,(apart 1).symm,(apart 2).symm,(apart 3).symm])]
    exact out t
  · intro j ne
    refine ⟨(congrFun left j).trans (frame j ne).1,?_⟩
    rw [right]
    split_ifs with hj
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl
      all_goals first | exact (empty 0).symm | exact (empty 1).symm | exact (empty 2).symm | exact (empty 3).symm
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hj
      simpa only [D,directorySpectatorState,Function.update_of_ne hj.1,Function.update_of_ne hj.2.1,
        Function.update_of_ne hj.2.2.1,Function.update_of_ne hj.2.2.2] using (frame j ne).2

/-- Reuse the child clock and the scratch released by the spectator conversion.
Private slots 2–5 still hold the spectator factors and their product. -/
def directoryModulusBank (K T : ℕ) (room : 16 ≤ T) : Fin 10 ↪ Fin (66+(K+3+T)) where
  toFun j := stoppedChartPrivate K T ⟨if j.val = 1 then 0 else 6+j.val,by split <;> omega⟩
  inj' := by
    intro i j eq
    apply Fin.ext
    have h := congrArg Fin.val eq
    change 66+K+3+(if i.val = 1 then 0 else 6+i.val) = 66+K+3+(if j.val = 1 then 0 else 6+j.val) at h
    split_ifs at h <;> omega

noncomputable def withChildModulus {T Q : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) (core : Pr P T Q prime U) :=
  ((childModulusWord r).seq core).seq (Prog.seqList ([r 2,r 3].map WordCmd.dropR))

open RecursiveInterchangeLayout in
theorem withChildModulus_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (owner : Fin T) (apart : ∀ i, r i ≠ owner) (batch : Descriptor)
    (hp : batch.Positive) (width : 0 < batch.width) (core : Pr P T Q prime U) (budget : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) (input word : Fin (volume prime batch) → ZMod 2)
    (payload : RecordPayload owner (fun _ => blank) 0 input S)
    (clock : (S.R (r 1)).length = batch.width/64-1) (free : ∀ i : Fin 10, i ≠ 1 → S.R (r i) = []) :
    let M := prime^(batch.width/64-1+1)
    let D := {S with R := Function.update (Function.update S.R (r 2) (List.replicate M Node.tick)) (r 3) (binSyms M.size M)}
    (∀ v : HS T Q prime U, RecordPayload owner (fun _ => blank) 0 input D →
      ∃ y B k, y.user = v.user ∧ k ≤ budget ∧ Exec body core (mk v D) k (mk y B) ∧
      RecordPayload owner (fun _ => blank) 0 word B ∧ ∀ j, j ≠ owner → B.L j = D.L j ∧ B.R j = D.R j) →
    ∃ z F k, z.user = u.user ∧ k ≤ budget+64*volume prime batch ∧
      Exec body (withChildModulus r core) (mk u S) k (mk z F) ∧ RecordPayload owner (fun _ => blank) 0 word F ∧
      ∀ j, j ≠ owner → F.L j = S.L j ∧ F.R j = S.R j := by
  intro M D child
  obtain ⟨v,n,user,paid,prep⟩ := childModulusWord_exec body r u S _ clock free
  obtain ⟨y,B,k,same,time,run,out,frame⟩ := child v (fun i => by
    simpa only [D,Function.update_of_ne (apart 2).symm,Function.update_of_ne (apart 3).symm] using payload i)
  obtain ⟨z,F,last,erase,left,right⟩ := retire_exec body [r 2,r 3] (by simp) y B
  have lengths (i : Fin 10) := congrArg List.length (frame _ (apart i)).2
  simp [lengths,D,length_binSyms] at erase
  refine ⟨z,F,_,last.trans (same.trans user),?_,Exec.seq (Exec.seq prep run) erase,?_,?_⟩
  · have pp := Shared50ModularControl.prime_prime.pos
    have hm : M ≤ prime^batch.width := pow_le_pow_right₀ pp (by omega)
    have scale : prime^batch.width ≤ volume prime batch := by
      obtain ⟨_,_,_,_,_⟩ := hp
      have h : 0 < batch.beforeRows*batch.rows*batch.beforeH*batch.between*prime^batch.width*batch.afterD := by positivity
      convert Nat.le_mul_of_pos_left (prime^batch.width) h using 1 <;> simp only [volume] <;> ring
    have bits : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
    have pos : 0 < M := pow_pos pp _
    change n ≤ 43*M+12 at paid
    omega
  · intro t
    rw [show F.L owner = B.L owner from congrFun left owner,right,ite_eq_right (by simp [(apart 2).symm,(apart 3).symm])]
    exact out t
  · intro j ne
    refine ⟨(congrFun left j).trans (frame j ne).1,?_⟩
    rw [right]
    by_cases a : j = r 2
    · subst j; simp [free 2 (by decide)]
    by_cases b : j = r 3
    · subst j; simp [free 3 (by decide)]
    simpa [D,a,b,Function.update_of_ne] using (frame j ne).2

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
    let replay := directoryChartReplayBank room
    let spectator := (directorySpectatorBank (K+1) LeafCore.small spectatorRoom).trans replay
    let modulus := (directoryModulusBank (K+1) LeafCore.small modulusRoom).trans replay
    withReplayPrefix prefixPorts (withDirectorySpectator spectator (withChildModulus modulus (node g)))

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
noncomputable def scheduledLeafCost [M8.Machine.Net] (scheduled : Descriptor) : ℝ :=
  let T := LeafCore.small
  ((223+((T+5 : ℕ)*|LeafCore.C|+8+T*(16+8*|LeafCore.C|)))*scheduled.width)*volume prime scheduled

open RecursiveInterchangeLayout in
noncomputable def scheduledBranchCost [M8.Machine.Net] (scheduled : Descriptor) (cutoff recursiveBudget : ℕ) : ℝ :=
  if cutoff < scheduled.width then (recursiveBudget : ℝ) else scheduledLeafCost scheduled

open RecursiveInterchangeLayout in
/-- The packed scanner requests an integral budget before calling its child. -/
noncomputable def scheduledChartBudget [M8.Machine.Net] (scheduled : Descriptor) (cutoff recursiveBudget : ℕ) : ℕ :=
  ⌊((1907*volume prime scheduled : ℕ) : ℝ)+scheduledBranchCost scheduled cutoff recursiveBudget⌋₊

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

open RecursiveInterchangeLayout in
theorem directorySpectatorBank_ready {K T n : ℕ} (room : 12 ≤ T)
    (replay : Fin (66+(K+3+T)) ↪ Fin n) (batch : Descriptor) (F : Stacks n prime)
    (ready : StoppedChartReady K T batch (embStk replay F)) (next : ℕ) :
    let r := (directorySpectatorBank K T room).trans replay
    let counts := (directoryChildCountBank K T (by omega)).trans replay
    let D := childCountState counts batch F
    let E := {D with R := Function.update D.R (replay ((58 : Fin 66).castAdd (K+3+T))) (List.replicate next Node.tick)}
    E.R (r 10) = (FlatCoordinateSchedule.bits batch.between).map bitSymbol ∧
      E.R (r 11) = (FlatCoordinateSchedule.bits batch.afterD).map bitSymbol ∧
      ∀ j : Fin 10, E.R (r (j.castAdd 2)) = [] := by
  intro r counts D E
  have keep (i : Fin 12) : E.R (r i) = F.R (r i) := by
    have off (j : Fin (66+(K+3+T))) (hj : j.val = 58 ∨ j.val = 66+K+3 ∨ j.val = 66+K+3+1) :
        r i ≠ replay j := by
      apply replay.injective.ne
      intro eq
      have h := congrArg Fin.val eq
      change (if i.val < 10 then 66+K+3+2+i.val else 27+i.val) = j.val at h
      split_ifs at h <;> omega
    exact (Function.update_of_ne (off _ (Or.inl rfl)) ..).trans
      ((Function.update_of_ne (off _ (Or.inr (Or.inr rfl))) ..).trans
        (Function.update_of_ne (off _ (Or.inr (Or.inl rfl))) ..))
  refine ⟨(keep 10).trans (ready.1 4), (keep 11).trans (ready.1 5), ?_⟩
  intro j
  rw [keep]
  have port : directorySpectatorBank K T room (j.castAdd 2) = stoppedChartPrivate K T ⟨2+j.val,by omega⟩ := by
    apply Fin.ext
    change (if j.val < 10 then _ else _) = _
    rw [if_pos j.isLt]
    change 66+K+3+2+j.val = 66+K+3+(2+j.val)
    omega
  exact (show F.R (replay (directorySpectatorBank K T room (j.castAdd 2))) = [] from
    port ▸ (ready.2 _).2)

open RecursiveInterchangeLayout in
theorem directoryModulusBank_ready {K T n : ℕ} (room : 16 ≤ T)
    (replay : Fin (66+(K+3+T)) ↪ Fin n) (batch : Descriptor) (F : Stacks n prime)
    (ready : StoppedChartReady K T batch (embStk replay F)) (next : ℕ) :
    let r := (directoryModulusBank K T room).trans replay
    let counts := (directoryChildCountBank K T (by omega)).trans replay
    let spec := (directorySpectatorBank K T (by omega)).trans replay
    let D := childCountState counts batch F
    let E := {D with R := Function.update D.R (replay ((58 : Fin 66).castAdd (K+3+T))) (List.replicate next Node.tick)}
    let G := directorySpectatorState spec batch.between batch.afterD E
    (G.R (r 1)).length = batch.width/64-1 ∧ ∀ j : Fin 10, j ≠ 1 → G.R (r j) = [] := by
  intro r counts spec D E G
  have off (i : Fin 10) (j : Fin (66+(K+3+T))) (hj : j.val = 58 ∨
      66+K+3+2 ≤ j.val ∧ j.val ≤ 66+K+3+5) : r i ≠ replay j := by
    apply replay.injective.ne
    intro eq
    have h := congrArg Fin.val eq
    change 66+K+3+(if i.val = 1 then 0 else 6+i.val) = j.val at h
    split_ifs at h <;> omega
  have kept (i : Fin 10) : G.R (r i) = D.R (r i) := by
    have hs (j : Fin 12) (small : j.val < 4) : r i ≠ spec j := by
      apply off i _ (Or.inr ?_)
      change _ ≤ (if j.val < 10 then 66+K+3+2+j.val else 27+j.val) ∧ _
      simp [directorySpectatorBank,show j.val < 10 by omega]
      omega
    simp only [G,E,directorySpectatorState,Function.update_of_ne (hs 0 (by decide)),
      Function.update_of_ne (hs 1 (by decide)),Function.update_of_ne (hs 2 (by decide)),
      Function.update_of_ne (hs 3 (by decide)),Function.update_of_ne (off i ((58 : Fin 66).castAdd (K+3+T)) (Or.inl rfl))]
  have clock : r 1 = counts 2 := rfl
  constructor
  · rw [kept,clock]
    simp [D,childCountState]
  · intro j hj
    rw [kept]
    have h : j.val ≠ 1 := fun eq => hj (Fin.ext eq)
    have pos : r j = replay (stoppedChartPrivate K T ⟨6+j.val,by omega⟩) := by
      apply congrArg replay
      apply Fin.ext
      simp [directoryModulusBank,stoppedChartPrivate,h]
    have ne (i : Fin 8) (hi : i = 2 ∨ i = 3) : r j ≠ counts i := by
      rw [pos]
      apply replay.injective.ne
      intro eq
      have bad := congrArg Fin.val eq
      rcases hi with rfl | rfl <;> simp [directoryChildCountBank,stoppedChartPrivate] at bad <;> omega
    simp only [D,childCountState,Function.update_of_ne (ne 3 (Or.inr rfl)),Function.update_of_ne (ne 2 (Or.inl rfl))]
    rw [pos]
    exact (ready.2 _).2

private theorem public_ne_saved {K T n : ℕ} (replay : Fin (66+(K+3+T)) ↪ Fin n)
    (i : Fin 66) (j : Fin 3) : replay (i.castAdd (K+3+T)) ≠ replay (stoppedChartHeader K T (j.castAdd 3)) := by
  apply replay.injective.ne
  intro eq
  have h := congrArg Fin.val eq
  change i.val = (if j.val < 3 then _ else _) at h
  rw [ite_eq_left j.isLt] at h
  omega

/-- Physical sources for an ordinary (unit-weight) child. The archive on 46
is still in parent order before the child's cyclic role split. -/
def childMetadataSources (K T : ℕ) (room : 16 ≤ T) : Fin 9 → Fin (66+(K+3+T)) :=
  let publicPort (i : Fin 66) := i.castAdd (K+3+T)
  let privatePort := stoppedChartPrivate K T
  ![privatePort ⟨9,by omega⟩,publicPort 29,privatePort ⟨1,by omega⟩,publicPort 31,
    privatePort ⟨0,by omega⟩,publicPort 58,privatePort ⟨5,by omega⟩,privatePort ⟨6,by omega⟩,publicPort 46]

/-- The caller's reusable tapes between the public ports and the saved headers. -/
def directoryChildWorkspace (K T : ℕ) : Fin K ↪ Fin (66+(K+3+T)) :=
  (Fin.natAddEmb 66).trans (Fin.castLEEmb (by omega))

theorem directoryChildWorkspace_off (K T : ℕ) (room : 16 ≤ T) (j : Fin K) :
    (∀ i, childMetadataSources K T room i ≠ directoryChildWorkspace K T j) ∧
    (40 : Fin 66).castAdd (K+3+T) ≠ directoryChildWorkspace K T j := by
  have high (i : Fin T) : stoppedChartPrivate K T i ≠ directoryChildWorkspace K T j := by
    intro eq
    have h := congrArg Fin.val eq
    change 66+K+3+i.val = 66+j.val at h
    omega
  have low (i : Fin 66) : i.castAdd (K+3+T) ≠ directoryChildWorkspace K T j := by
    intro eq
    have h := congrArg Fin.val eq
    change i.val = 66+j.val at h
    omega
  exact ⟨by intro i; fin_cases i <;> first | apply high | apply low,low 40⟩

open RecursiveInterchangeLayout in
theorem childMetadataSources_words {K T n w rows : ℕ} (room : 16 ≤ T)
    (replay : Fin (66+(K+3+T)) ↪ Fin n) (batch : Descriptor) (F : Stacks n prime)
    (ready : StoppedChartReady K T batch (embStk replay F)) (next : ℕ)
    (width : batch.width = 64*(w+1)) (split : batch.rows = 142080*rows)
    (outer : F.R (replay ((29 : Fin 66).castAdd (K+3+T))) = List.replicate batch.beforeRows Node.tick)
    (labels : F.R (replay ((31 : Fin 66).castAdd (K+3+T))) = List.replicate batch.beforeH Node.tick) :
    let publicPort (i : Fin 66) := replay (i.castAdd (K+3+T))
    let counts := (directoryChildCountBank K T (by omega)).trans replay
    let spectator := (directorySpectatorBank K T (by omega)).trans replay
    let modulus := (directoryModulusBank K T room).trans replay
    let D := childCountState counts batch F
    let E := {D with R := Function.update D.R (publicPort 58) (List.replicate next Node.tick)}
    let G := directorySpectatorState spectator batch.between batch.afterD E
    let M := prime^(batch.width/64-1+1)
    let B := {G with R := Function.update (Function.update G.R (modulus 2) (List.replicate M Node.tick)) (modulus 3) (binSyms M.size M)}
    let words := ordinaryEntryWords (batch.between*batch.afterD) batch.beforeRows rows batch.beforeH true
      (fun _ => (1 : ZMod (prime^(w+1)))) next (F.R (publicPort 46))
    B.R (publicPort 40) = F.R (publicPort 40) ∧
      (∀ j : Fin (66+(K+3+T)), 66 ≤ j.val → j.val < 66+K →
        B.L (replay j) = F.L (replay j) ∧ B.R (replay j) = F.R (replay j)) ∧
      ∀ i : Fin 9, B.R (replay (childMetadataSources K T room i)) = words (ordinaryMetadataPorts i).val := by
  intro publicPort counts spectator modulus D E G M B words
  have clock : batch.width/64-1 = w := by omega
  have count : batch.rows/142080 = rows := by omega
  let priv (i : Fin 16) := replay (stoppedChartPrivate K T (i.castLE room))
  have pp {i j : Fin 16} (h : i ≠ j) : priv i ≠ priv j := by
    apply replay.injective.ne
    intro eq
    apply h
    exact Fin.ext (by have e := congrArg Fin.val eq; change 66+K+3+i.val = 66+K+3+j.val at e; omega)
  have separate (i : Fin 66) (j : Fin 16) : publicPort i ≠ priv j := by
    apply replay.injective.ne
    intro eq
    have e := congrArg Fin.val eq
    change i.val = 66+K+3+j.val at e
    omega
  have pub {i j : Fin 66} (h : i ≠ j) : publicPort i ≠ publicPort j :=
    ((Fin.castAddEmb (K+3+T)).trans replay).injective.ne h
  have spare : F.R (priv 6) = [] := (ready.2 _).2
  have state : B.R = Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update F.R
        (priv 0) (List.replicate w Node.tick)) (priv 1) (List.replicate rows Node.tick)) (publicPort 58) (List.replicate next Node.tick))
        (priv 2) (List.replicate batch.between Node.tick)) (priv 3) (List.replicate batch.afterD Node.tick))
        (priv 4) (List.replicate (batch.between*batch.afterD) Node.tick))
        (priv 5) (binSyms (batch.between*batch.afterD).size (batch.between*batch.afterD)))
        (priv 8) (List.replicate (prime^(w+1)) Node.tick)) (priv 9) (binSyms (prime^(w+1)).size (prime^(w+1))) := by
    dsimp only [B,G,E,D,M,directorySpectatorState,childCountState]
    rw [clock,count]
    rfl
  change F.R (publicPort 29) = _ at outer
  change F.R (publicPort 31) = _ at labels
  rw [state]
  have sources : (fun i => replay (childMetadataSources K T room i)) =
      ![priv 9,publicPort 29,priv 1,publicPort 31,priv 0,publicPort 58,priv 5,priv 6,publicPort 46] := by
    funext i; fin_cases i <;> rfl
  refine ⟨by simp [Function.update_of_ne,separate,pub],?_,?_⟩
  · intro j low high
    have off (i : Fin 16) : replay j ≠ priv i := by
      apply replay.injective.ne
      intro eq
      have h := congrArg Fin.val eq
      change j.val = 66+K+3+i.val at h
      omega
    have publicOff : replay j ≠ publicPort 58 := by
      apply replay.injective.ne
      intro eq
      have h := congrArg Fin.val eq
      change j.val = 58 at h
      omega
    exact ⟨rfl,by simp [Function.update_of_ne,off,publicOff]⟩
  intro i
  rw [show replay (childMetadataSources K T room i) = _ from congrFun sources i]
  fin_cases i <;> simp [words,ordinaryMetadataPorts,ordinaryEntryWords,Function.update_of_ne,
    pp, pub, separate, fun i j => (separate i j).symm,outer,labels,spare,Node.tick]

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Install both directory passes and the cutoff selector on their shared chart bank. -/
theorem selectScheduledChart_exec [M8.Machine.Net] (K : ℕ) {P R U : Type}
    (room : Record.size 127+(rowSwapBlock.tapes+35+2) ≤ ((K+1)+3+LeafCore.small)+1)
    (localBody : P → Pr P (66+((K+1)+3+LeafCore.small)) columnCapacity prime U)
    (node : Descriptor) (window : Fin 9) (job : Fin idleCopies.length) (w cutoff : ℕ)
    (root : Descriptor) (depth b blocks : ℕ) (levels : 0 < depth) (base : 0 < b)
    (rootWidth : root.width = 64^depth*b) (rootRows : 142080^depth ∣ root.rows)
    (stop : 42^depth*b ≤ cutoff) (within : cutoff ≤ root.width)
    (path : List (Fin nodeChildren5.length))
    (pathWidth : (path.foldl (scheduledChild prime) root).width = node.width)
    (pathRows : (path.foldl (scheduledChild prime) root).rows = node.rows)
    (labels : node.beforeH = blocks*prime^(64*node.width))
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) :
    let i := idleDirectoryIndex (window,job)
    let interval := idleInterval window idleCopies[job.val].2
    let lo := interval.1
    let hi := interval.2
    let rank : hi-lo = (nodeChildren5[i.val]'(i.isLt)) := (idleDirectoryIndex_rank window job).symm
    let L := root.width.size
    let parent := role node 142080
    let batch := ordinaryDirectoryChild parent (nodeChildren5[i.val]'(i.isLt)) (64-(nodeChildren5[i.val]'(i.isLt))) w
    let row := remainderRecordChild lo hi (w+1) (parent.between*parent.afterD)
    let scheduled := scheduledChild prime node i
    let T := LeafCore.small
    let tapes := 66+(((K+1)+3+T)+1)
    let owner := (0 : Fin 5).natAdd (tapes+10)
    let host := directoryChartHost room localBody (stoppedChartChild (K+1))
    let replay := directoryChartReplayBank room
    ∀ (recursive : R → Pr ((P ⊕ (P ⊕ Unit)) ⊕ (Fin 43 ⊕ R)) ((tapes+10)+5) columnCapacity prime U) (f : R) (recursiveBudget : ℕ),
    let procedures := scheduledChartProcedures K room localBody recursive f
    let body := recursiveChartTable host procedures
    ∀ {W H J : ℕ} {proj : Matrix (Fin 64) (Fin 64) ℚ} {weights : Fin 64 → ZMod (prime^(w+1))}
      {prefixes : ℕ → List (Fin (prime+4))}, 0 < volume prime node → cutoff < node.width →
      (∀ x : Fin (volume prime batch) → ZMod 2,
        cutoff < batch.width → batch.width < node.width → batch.Positive →
        ∀ (z : HS ((tapes+10)+5) columnCapacity prime U) (B : Stacks ((tapes+10)+5) prime),
        let next := directoryDigits prime root (path++[i])
        let e := batch.width/64-1
        let rows := batch.rows/142080
        (List.foldl (scheduledChild prime) root (path++[i])).width = batch.width →
        (List.foldl (scheduledChild prime) root (path++[i])).rows = batch.rows →
        batch.beforeH = (blocks*prime^(64*(node.width-batch.width)))*prime^(64*((e+1)*64)) →
        batch.width = 64*(e+1) → batch.rows = 142080*rows →
        next ≤ prime^batch.width →
        B.R (replay ((40 : Fin 66).castAdd ((K+1)+3+T))) = binSyms L cutoff →
        (B.R (replay ((40 : Fin 66).castAdd ((K+1)+3+T)))).length ≤ batch.width →
        (∀ j : Fin (K+1), let i := replay (directoryChildWorkspace (K+1) T j)
          B.L i = [] ∧ B.R i = []) →
        (∀ j < batch.beforeRows*rows*142080*batch.beforeH,
          (LabelDirectory.entry prefixes 64 (w+1) j).length = next ∧ blank ∉ LabelDirectory.entry prefixes 64 (w+1) j) →
        (∀ j : Fin 9, B.R (replay (childMetadataSources (K+1) T modulusRoom j)) =
            ordinaryEntryWords (batch.between*batch.afterD) batch.beforeRows rows batch.beforeH true
              (fun _ => (1 : ZMod (prime^(e+1)))) next
              ((List.range (batch.beforeRows*rows*142080*batch.beforeH)).flatMap (LabelDirectory.entry prefixes 64 (w+1)))
              (ordinaryMetadataPorts j).val) →
        RecordPayload owner (fun _ => blank) 0 x B →
        ∃ y J, ∃ k : ℕ, y.user = z.user ∧ k ≤ recursiveBudget ∧
          Exec body (recursive f) (mk z B) k (mk y J) ∧
          RecordPayload owner (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) J ∧
          ∀ j, j ≠ owner → J.L j = B.L j ∧ J.R j = B.R j) →
      DirectoryChartCall room localBody body (Sum.inl ∘ Sum.inl) (Sum.inl ∘ (Sum.inr ∘ Sum.inl))
        (.inr (.inl ⟨hi-lo,rank.symm ▸ Nat.lt_succ_of_le (nodeChildren5_le i)⟩)) parent row
        (ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w) W H J (directoryDigits prime root path)
        (scheduledChartBudget scheduled cutoff recursiveBudget) proj weights prefixes (binSyms L cutoff) := by
  intro i interval lo hi rank L parent batch row scheduled T tapes owner host replay recursive f recursiveBudget procedures body
    W H J proj weights prefixes positive activeParent recursiveRun
  have handlers := recursiveChartTable_scan room localBody (stoppedChartChild (K+1)) procedures
  have sameBatch : ordinaryDirectoryChild parent (hi-lo) (64-(hi-lo)) w = batch :=
    congrArg (fun r => ordinaryDirectoryChild parent r (64-r) w) rank
  rw [sameBatch]
  refine ⟨handlers.1,handlers.2,?_⟩
  intro a A x prefixWidth clean directoryReady cutWord src payload
  let pending := List.range (LabelMask.records parent)
  have recurse := recursiveRun x
  let values : Fin 3 → ℕ := ![parent.beforeRows,parent.rows,parent.beforeH]
  let leafBudget := scheduledLeafCost scheduled
  obtain ⟨cutFits, fits, precision⟩ := scheduledChartPrecision root depth b cutoff levels base rootWidth stop within path i
  change (nodeChildren5[i.val]*((path.foldl (scheduledChild prime) root).width/64)).size ≤ L at fits
  rw [pathWidth] at fits
  let counts := (directoryChildCountBank (K+1) T (show 6 ≤ T from (by decide : 6 ≤ 9).trans nine_le_leaf)).trans replay
  let prefixPorts := (childPrefixPorts.trans (Fin.castAddEmb ((K+1)+3+T))).trans replay
  let saved := fun j : Fin 3 => replay (stoppedChartHeader (K+1) T (j.castAdd 3))
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
    change (directoryOuterWords (embStk replay A) j).length = values j
    simpa only [List.length_replicate] using congrArg List.length (src j)
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
    (if cutoff < scheduled.width then (recursiveBudget : ℝ)+(419*volume prime scheduled : ℕ)+2 else leafBudget)
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
        ((recursiveBudget+64*volume prime batch+133*volume prime batch+28*volume prime batch+2)+81*volume prime batch) z A
      rw [rank] at prepared
      obtain ⟨_,nextWidth,nextRows,nextFits,prefixFits,childWidth,childRows,nextLabels,recordCount⟩ := activeBatchChartDimensions
        root node depth b cutoff blocks levels base rootWidth rootRows stop path i w aligned rows positive
        pathWidth pathRows labels (batchWidth.symm ▸ active)
      have recordPos : 0 < LabelMask.records parent := Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2.1
      have prefixSize := (directoryReady.2.1 0 (List.mem_range.mpr recordPos)).trans prefixWidth
      change (A.R (prefixPorts 0)).length = directoryDigits prime root path at prefixSize
      have call := recurse (batchWidth.symm ▸ active) (batchWidth.symm ▸ smaller) batchPos
      obtain ⟨y,B,k,user,paid,execution,out,frame⟩ := prepared x sources empty tail free payload (by
        intro v F ready keep input
        have registers := directoryChildCountBank_ready (K := K+1) (T := T) ((by decide : 6 ≤ 9).trans nine_le_leaf)
          replay batch F ready
        apply withChildCounts_exec body counts owner (fun j => apart _) batch (batchSize.symm ▸ pos) (.call (.inr (.inr f)))
          (recursiveBudget+64*volume prime batch+133*volume prime batch+28*volume prime batch+2) v F _ registers.1 registers.2.1 registers.2.2
        intro v'
        have childInput : RecordPayload owner (fun _ => blank) 0 x (childCountState counts batch F) := by
          intro t
          have ne₂ : owner ≠ counts 2 := (apart _).symm
          have ne₃ : owner ≠ counts 3 := (apart _).symm
          simpa only [childCountState, Function.update_of_ne ne₃, Function.update_of_ne ne₂] using input t
        have publicWords := childCountState_public ((by decide : 6 ≤ 9).trans nine_le_leaf) replay batch A F keep
        have fitsHere : (A.R (prefixPorts 0)).length+(w+1)*(64*64) ≤ volume prime batch := prefixSize.symm ▸ prefixFits
        have hclock := publicWords 47
        change (childCountState counts batch F).R (prefixPorts 0) = A.R (prefixPorts 0) at hclock
        let r := (directorySpectatorBank (K+1) T spectatorRoom).trans replay
        let modulus := (directoryModulusBank (K+1) T modulusRoom).trans replay
        obtain ⟨y,B,k,user,time,run,out,frame⟩ := withReplayPrefix_exec body replay owner apart row proj weights prefixes
          pending v' (childCountState counts batch F) (embStk replay A) directoryReady publicWords (withDirectorySpectator r (withChildModulus modulus (recursive f))) (recursiveBudget+64*volume prime batch+133*volume prime batch)
          x (Shared50RecursiveNodeRows.transpose (one_dvd batch.rows) x) childInput
          (by change ((childCountState counts batch F).R (prefixPorts 0)).length+_ ≤ _; rwa [hclock])
          (by
            intro z archive widths word
            obtain ⟨between,afterD,empty⟩ := directorySpectatorBank_ready spectatorRoom replay batch F ready
              (((childCountState counts batch F).R (prefixPorts 0)).length+(w+1)*(64*64))
            apply withDirectorySpectator_exec body r owner (fun j => apart _) batch batchPos
              (withChildModulus modulus (recursive f)) (recursiveBudget+64*volume prime batch) z _ x _ word between afterD empty
            intro v incoming
            obtain ⟨clock,free⟩ := directoryModulusBank_ready modulusRoom replay batch F ready
              (((childCountState counts batch F).R (prefixPorts 0)).length+(w+1)*(64*64))
            apply withChildModulus_exec body modulus owner (fun j => apart _) batch batchPos
              (Nat.zero_lt_of_lt (batchWidth.symm ▸ active)) (recursive f) recursiveBudget v _ x _ incoming clock free
            intro y
            have length : ((childCountState counts batch F).R (prefixPorts 0)).length+(w+1)*(64*64) = directoryDigits prime root (path++[i]) := by
              rw [hclock,prefixSize,directoryDigits_append_call,pathWidth,aligned]
              simp
            obtain ⟨cutoffKept,privateKept,metadata⟩ := childMetadataSources_words modulusRoom replay batch F ready
              (((childCountState counts batch F).R (prefixPorts 0)).length+(w+1)*(64*64)) childWidth childRows
              (((keep _ (public_ne_saved replay 29)).2).trans (src 0))
              (((keep _ (public_ne_saved replay 31)).2).trans (src 2))
            have cutoffWord := cutoffKept.trans (((keep _ (public_ne_saved replay 40)).2).trans cutWord)
            apply call y _ nextWidth nextRows nextLabels childWidth childRows nextFits cutoffWord
            · rw [cutoffWord,length_binSyms]
              exact precision.trans (batchWidth.symm ▸ active.le)
            · intro slot
              let j := directoryChildWorkspace (K+1) T slot
              have low : 66 ≤ j.val := by change 66 ≤ 66+slot.val; omega
              have high : j.val < 66+(K+1) := by change 66+slot.val < _; omega
              have original := directoryReady.2.2.1 j (by omega)
              have kept := keep (replay j) (fun l => by
                apply replay.injective.ne
                intro eq
                have h := congrArg Fin.val eq
                simp only [stoppedChartHeader,Fin.val_castAdd,ite_eq_left l.isLt] at h
                omega)
              obtain ⟨left,right⟩ := privateKept j low high
              exact ⟨left.trans (kept.1.trans original.1),right.trans (kept.2.trans original.2)⟩
            · intro j hj
              have mem : j ∈ pending := List.mem_range.mpr (recordCount.symm ▸ hj)
              refine ⟨(widths j mem).trans (Eq.trans ?_ length), directoryEntry_nonblank _ _ _ _ (clean j mem)⟩
              simp only [prefixPorts,T,Function.update_self,List.length_replicate]
            have archiveWord := ((keep _ (public_ne_saved replay 46)).2).trans (directoryReady.1.trans (List.append_nil _))
            change F.R (replay ((46 : Fin 66).castAdd ((K+1)+3+T))) = (List.range (LabelMask.records parent)).flatMap _ at archiveWord
            rw [recordCount] at archiveWord
            rw [← archiveWord]
            simpa only [← length] using metadata)
        exact ⟨y,B,k+2,user,Nat.add_le_add_right time 2,Exec.call run,out,frame⟩)
      obtain ⟨count,erase⟩ := directoryHeaderCosts parent nodeChildren5[i.val] (64-nodeChildren5[i.val]) w (batchSize.symm ▸ pos)
      have bound : k ≤ 419*volume prime scheduled + recursiveBudget+2 := by
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
    (recursive := (recursiveBudget : ℝ)+(419*volume prime scheduled : ℕ)) (leaf := leafBudget) (L := L)
  have parentBound := Nat.mul_le_mul_left 64 (atomBound.trans size)
  have scaled : 80*volume prime scheduled+22*L+419*volume prime scheduled ≤ 1907*volume prime scheduled := by omega
  have cost := paid.trans comparison
  refine ⟨y,B,k,user,?_,execution,out,frame⟩
  change k ≤ ⌊((1907*volume prime scheduled : ℕ) : ℝ)+(if cutoff < scheduled.width then (recursiveBudget : ℝ) else leafBudget)⌋₊
  apply Nat.le_floor
  have slack := (Nat.cast_le (α := ℝ)).mpr scaled
  have nonneg : (0 : ℝ) ≤ volume prime scheduled := Nat.cast_nonneg _
  split_ifs at cost ⊢ <;> push_cast at cost slack ⊢ <;> linarith


open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- Sum the selector costs over the directory occurrences of a parent. Each
selected child budget is charged once, independently of its stopping decision. -/
theorem scheduledChartDispatch_sum [M8.Machine.Net] (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (calls : Finset (Fin nodeChildren5.length)) (cutoff : ℕ) (recursiveBudget : Fin nodeChildren5.length → ℕ) :
    let child := scheduledChild prime node
    ∑ i ∈ calls, (scheduledChartBudget (child i) cutoff (recursiveBudget i) : ℝ) ≤
      (calls.card*1907/142080 : ℝ)*volume prime node + ∑ i ∈ calls, scheduledBranchCost (child i) cutoff (recursiveBudget i) := by
  intro child
  have paid (i) : (scheduledChartBudget (child i) cutoff (recursiveBudget i) : ℝ) ≤
      ((1907*volume prime (child i) : ℕ) : ℝ)+scheduledBranchCost (child i) cutoff (recursiveBudget i) := by
    apply Nat.floor_le
    unfold scheduledBranchCost scheduledLeafCost
    split_ifs <;> positivity
  have share (i : Fin nodeChildren5.length) : (volume prime (scheduledChild prime node i) : ℝ)*142080 = volume prime node := by
    exact_mod_cast (scheduledChild_measures prime node width rows i).2
  have price (i) : ((1907*volume prime (scheduledChild prime node i) : ℕ) : ℝ) =
      (1907/142080 : ℝ)*volume prime node := by
    rw [← share i]
    push_cast
    ring
  calc
    _ ≤ ∑ i ∈ calls, (((1907*volume prime (scheduledChild prime node i) : ℕ) : ℝ)+scheduledBranchCost (child i) cutoff (recursiveBudget i)) := Finset.sum_le_sum (fun i _ => paid i)
    _ = _ := by simp only [price,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]; ring

open IntegerMultBounds.Networks.Certificates.PR589.Nine RecursiveInterchangeLayout in
/-- The nine physical idle passes charge their own branch budgets. The other
occurrences retain their entire branch budgets for the stage pieces. -/
theorem scheduledIdleTime [M8.Machine.Net] (node : Descriptor) (width : 64 ∣ node.width) (rows : 142080 ∣ node.rows)
    (cutoff : ℕ) (recursiveBudget : Fin nodeChildren5.length → ℕ) (time : Fin 9 → ℝ)
    (bill : Fin 9 → (Fin 32 × Fin 5) × Fin 222 → ℝ) (overhead : Fin 9 × Fin idleCopies.length → ℝ) :
    let child := scheduledChild prime node
    let branch := fun i => scheduledBranchCost (child i) cutoff (recursiveBudget i)
    let calls := Finset.univ.map idleDirectoryIndex
    (∀ i, time i ≤ (idleCopies.map (bill i)).sum+1) →
    (∀ k : Fin 9 × Fin idleCopies.length, let i := idleDirectoryIndex k
      bill k.1 idleCopies[k.2.val] ≤ overhead k+scheduledChartBudget (child i) cutoff (recursiveBudget i)) →
    (∑ i, time i) + (∑ j ∈ callsᶜ, branch j) ≤
      (∑ k, overhead k) + (9*1907/4 : ℝ)*volume prime node + (∑ j, branch j) + 9 := by
  classical
  intro child branch calls passes paid
  let budget := fun j => (scheduledChartBudget (child j) cutoff (recursiveBudget j) : ℝ)
  have total := idleDirectoryTime time bill overhead budget passes paid
  have stages := Finset.sum_add_sum_compl calls budget
  have selectors := scheduledChartDispatch_sum node width rows calls cutoff recursiveBudget
  change (∑ i ∈ calls, budget i) ≤ _ + ∑ i ∈ calls, branch i at selectors
  have branches := Finset.sum_add_sum_compl calls branch
  change (∑ i, time i) + (∑ j ∈ callsᶜ, budget j) ≤ _ at total
  have card : calls.card = 319680 := by
    simp only [calls,Finset.card_map,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,idleCopies_length]
  rw [card] at selectors
  norm_num at selectors ⊢
  linarith only [total,stages,selectors,branches]

end IntegerMultBounds.MathlibTM2.M6.BitNode
