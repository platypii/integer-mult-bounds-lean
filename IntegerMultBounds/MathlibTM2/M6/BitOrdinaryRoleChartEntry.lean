module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryChildCounts
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryIdleRead

/-! Prepare the smaller PR589 chart from the inherited archive and child metadata. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host M8.RevMachine
open Shared50ModularControl (prime)
open FlatCoordinateLayout LabelTraversal Matrix M8.Exchange IntegerMultBounds.Swap.Modular
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

def splitCountSlots (groups : Bool) : Fin 10 ↪ Fin 14 :=
  ⟨if groups then ![2,3,6,7,8,9,10,11,12,13] else ![0,1,4,5,8,9,10,11,12,13],
    by cases groups <;> decide⟩

noncomputable def splitCountWord {T Q : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) : Pr P T Q prime U :=
  (Mult.ShortConv.unaryProduct (r 0) (r 1) (r 2) (r 4) (r 5)).seq
    (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9))

/-- Form the two split counters from the child's metadata. Both products use
the same six work tapes. Multiplying by the positive label count also covers
the empty-prefix case. -/
theorem childRoleSplitCounts_exec {T Q w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 14 ↪ Fin T) (u : HS T Q prime U) (S : Stacks T prime)
    (W a rows H width : ℕ) (positive : 0 < H) (rowCount : 0 < rows) (archive : List (Fin (prime+4))) :
    let words := ordinaryEntryWords W a rows H true (fun _ => (1 : ZMod (prime^(w+1)))) width archive
    S.R (r 0) = words 47 → S.R (r 1) = words 31 → S.R (r 2) = words 29 → S.R (r 3) = words 30 →
    (∀ j : Fin 14, 4 ≤ j.val → S.R (r j) = []) →
    let symbols := H*width
    let groups := a*rows
    let D := {S with R := Function.update (Function.update S.R (r 4) (List.replicate symbols Node.tick)) (r 5) (binSyms symbols.size symbols)}
    ∃ z k, z.user = u.user ∧ k ≤ 34*(symbols+groups)+28 ∧
      Exec body ((splitCountWord ((splitCountSlots false).trans r)).seq (splitCountWord ((splitCountSlots true).trans r)))
        (mk u S) k (mk z {D with R := Function.update (Function.update D.R (r 6) (List.replicate groups Node.tick)) (r 7) (binSyms groups.size groups)}) := by
  intro words widthWord labelWord outerWord rowWord free symbols groups D
  have firstFree (j : Fin 10) (hj : 2 ≤ j.val) : 4 ≤ (splitCountSlots false j).val := by
    revert hj; fin_cases j <;> decide
  obtain ⟨v,n,user,paid,first⟩ := ordinarySpectatorWord_exec body ((splitCountSlots false).trans r) u S width H
    (by change (S.R (r 0)).length = _; simp [widthWord,words,ordinaryEntryWords])
    (by change (S.R (r 1)).length = _; simp [labelWord,words,ordinaryEntryWords]) positive
    (fun j hj => free _ (firstFree j hj))
  rw [Nat.mul_comm width H] at first paid
  have same (j : Fin 10) : D.R (r (splitCountSlots true j)) = S.R (r (splitCountSlots true j)) :=
    (Function.update_of_ne (r.injective.ne (by fin_cases j <;> decide)) ..).trans
      (Function.update_of_ne (r.injective.ne (by fin_cases j <;> decide)) ..)
  have secondFree (j : Fin 10) (hj : 2 ≤ j.val) : 4 ≤ (splitCountSlots true j).val := by
    revert hj; fin_cases j <;> decide
  obtain ⟨z,m,last,time,second⟩ := ordinarySpectatorWord_exec body ((splitCountSlots true).trans r) v D a rows
    (by rw [show (D.R (((splitCountSlots true).trans r) 0)) = _ from same 0]; change (S.R (r 2)).length = _; simp [outerWord,words,ordinaryEntryWords])
    (by rw [show (D.R (((splitCountSlots true).trans r) 1)) = _ from same 1]; change (S.R (r 3)).length = _; simp [rowWord,words,ordinaryEntryWords])
    rowCount (fun j hj => (same j).trans (free _ (secondFree j hj)))
  exact ⟨z,n+m,last.trans user,by dsimp only [symbols,groups]; omega,Exec.seq first second⟩

/-- The binary products go straight to the two descriptor tapes. The four
unary inputs, two unary products and six temporary tapes lie outside the split. -/
def roleSplitCountBank (c : ℕ) : Fin 14 ↪ Fin ((((1+c)+2)+2)+12) :=
  let offset : Fin 14 ↪ Fin 17 := ⟨![5,6,7,8,9,2,10,4,11,12,13,14,15,16],by decide⟩
  offset.trans ((Fin.natAddEmb c).trans (Fin.castOrderIso (by omega)).toEquiv.toEmbedding)

/-- Prepare and release the unary products. Only the two binary counters
remain when the splitter takes control of the bank. -/
theorem prepareSplitHeaders_exec {T Q w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 14 ↪ Fin T) (u : HS T Q prime U) (S : Stacks T prime)
    (W a rows H width : ℕ) (positive : 0 < H) (rowCount : 0 < rows) (archive : List (Fin (prime+4))) :
    let words := ordinaryEntryWords W a rows H true (fun _ => (1 : ZMod (prime^(w+1)))) width archive
    S.R (r 0) = words 47 → S.R (r 1) = words 31 → S.R (r 2) = words 29 → S.R (r 3) = words 30 →
    (∀ j : Fin 14, 4 ≤ j.val → S.R (r j) = []) →
    let symbols := H*width
    let groups := a*rows
    let prep := (splitCountWord ((splitCountSlots false).trans r)).seq (splitCountWord ((splitCountSlots true).trans r))
    ∃ z F k, z.user = u.user ∧ k ≤ 36*(symbols+groups)+33 ∧
      Exec body (prep.seq (Prog.seqList ([r 4,r 6].map WordCmd.dropR))) (mk u S) k (mk z F) ∧
      F.L = S.L ∧ F.R = Function.update (Function.update S.R (r 5) (binSyms symbols.size symbols))
        (r 7) (binSyms groups.size groups) := by
  intro words widthWord labelWord outerWord rowWord free symbols groups prep
  obtain ⟨v,k,user,paid,run⟩ := childRoleSplitCounts_exec (w := w) body r u S W a rows H width positive rowCount archive
    widthWord labelWord outerWord rowWord free
  let D := Function.update (Function.update S.R (r 4) (List.replicate symbols Node.tick)) (r 5) (binSyms symbols.size symbols)
  let B := {S with R := Function.update (Function.update D (r 6) (List.replicate groups Node.tick)) (r 7) (binSyms groups.size groups)}
  obtain ⟨z,F,last,erase,left,right⟩ := retire_exec body [r 4,r 6] (by simp) v B
  simp [B,D] at erase
  have both := Exec.seq run erase
  refine ⟨z,F,_,last.trans user,?_,both,left,funext fun j => ?_⟩
  · dsimp only [symbols,groups]; omega
  · rw [right]
    by_cases j₄ : j = r 4
    · subst j; simp [free 4 (by decide)]
    by_cases j₆ : j = r 6
    · subst j; simp [free 6 (by decide)]
    by_cases j₅ : j = r 5
    · subst j; simp [B,D]
    by_cases j₇ : j = r 7
    · subst j; simp [B,D]
    simp [B,D,j₄,j₅,j₆,j₇,Function.update_of_ne]

noncomputable def childRoleQueueProgram {N Q : ℕ} {P U : Type}
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (place : Fin ((((1+142080)+2)+2)+12) ↪ Fin N) (incoming : Fin N) (j : Fin 142080) : Pr P N Q prime U :=
  let T := ((1+142080)+2)+2
  let bank := (Fin.castAddEmb (n := T) 12).trans place
  let r := (roleSplitCountBank 142080).trans place
  let src := (((0 : Fin (1+142080)).castAdd 2).castAdd 2)
  let copy : Pr P N Q prime U := bcopy incoming (bank src) (bank 1) (bank 2)
  let port := ((j.natAdd 1).castAdd 2).castAdd 2
  let fields := (List.finRange 4).map (roleSplitControls 142080)
  let prep := ((splitCountWord ((splitCountSlots false).trans r)).seq (splitCountWord ((splitCountSlots true).trans r))).seq
    (Prog.seqList ([r 4,r 6].map WordCmd.dropR))
  let split : Pr Empty T Q prime U := (Prog.act (pushMarkers fields)).seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))
  (prep.seq copy).seq (embProg bank Empty.elim (split.seq (normTape port)))

/-- On a shared placement, generate the counters, split the inherited archive,
and materialize the chosen role queue. Everything outside the splitter is
restored, including all arithmetic workspace and the four dimension inputs. -/
theorem childRoleQueue_exec {N Q w : ℕ} {P U : Type}
    (body : P → Pr P N Q prime U) (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (place : Fin ((((1+142080)+2)+2)+12) ↪ Fin N) (incoming : Fin N) (u : HS N Q prime U) (S : Stacks N prime)
    (W a rows H width V : ℕ) (outer : 0 < a) (rowCount : 0 < rows) (labels : 0 < H)
    (row : 0 < V) (fits : width ≤ V) (archive : ℕ → List (Fin (prime+4)))
    (widths : ∀ k < a*rows*142080*H, (archive k).length = width)
    (clean : ∀ k < a*rows*142080*H, blank ∉ archive k) (j : Fin 142080) :
    let T := ((1+142080)+2)+2
    let bank := (Fin.castAddEmb (n := T) 12).trans place
    let r := (roleSplitCountBank 142080).trans place
    let input := (List.range (a*rows*142080*H)).flatMap archive
    let words := ordinaryEntryWords W a rows H true (fun _ => (1 : ZMod (prime^(w+1)))) width input
    let port := ((j.natAdd 1).castAdd 2).castAdd 2
    S.R (r 0) = words 47 → S.R (r 1) = words 31 → S.R (r 2) = words 29 → S.R (r 3) = words 30 →
    (∀ i : Fin 14, 4 ≤ i.val → S.R (r i) = []) →
    (∀ i, S.L (bank i) = []) → S.R incoming = input → (∀ i, bank i ≠ incoming) → (∀ i, S.R (bank i) = []) →
    ∃ z F k, z.user = u.user ∧
      k ≤ 36*(H*width+a*rows)+52+(149*(T+5)+1794)*(a*rows*142080*H*V) ∧
      Exec body (childRoleQueueProgram capacity place incoming j) (mk u S) k (mk z F) ∧
      F.L (bank port) = [] ∧ F.R (bank port) = directoryChartQueue (some j) H 0 (a*rows*H) archive ∧
      ∀ i, (∀ l, bank l ≠ i) → F.L i = S.L i ∧ F.R i = S.R i := by
  intro T bank r input words port widthWord labelWord outerWord rowWord free left source outside empty
  let src := (((0 : Fin (1+142080)).castAdd 2).castAdd 2)
  obtain ⟨v,B,m,user,price,setup,bl,br⟩ := prepareSplitHeaders_exec (w := w) body r u S W a rows H width
    labels rowCount input widthWord labelWord outerWord rowWord free
  let ctrl := (roleSplitControls 142080).trans bank
  have h₁ : r 5 = ctrl 1 := rfl
  have h₃ : r 7 = ctrl 3 := rfl
  rw [h₁,h₃] at br
  have off (i : Fin T) (hi : ∀ l, roleSplitControls 142080 l ≠ i) : B.R (bank i) = S.R (bank i) :=
    (congrFun br _).trans ((Function.update_of_ne (bank.injective.ne (hi 3).symm) ..).trans
      (Function.update_of_ne (bank.injective.ne (hi 1).symm) ..))
  have below (i : Fin (1+142080)) (l : Fin 4) : roleSplitControls 142080 l ≠ (i.castAdd 2).castAdd 2 := by
    intro eq
    have bad := congrArg Fin.val eq
    change 1+142080+l.val = i.val at bad
    omega
  have hdr (i : Fin 4) : B.R (ctrl i) =
      ![[],binSyms (H*width).size (H*width),[],binSyms (a*rows).size (a*rows)] i := by
    rw [br]
    have unused (l : Fin 4) : S.R (ctrl l) = [] := empty _
    fin_cases i <;> simp [unused]
  have inputWord : B.R incoming = input := by
    have ne (i : Fin 4) : incoming ≠ ctrl i := (outside _).symm
    rw [br,Function.update_of_ne (ne 3),Function.update_of_ne (ne 1),source]
  have init (i : Fin (1+142080)) : B.R (bank ((i.castAdd 2).castAdd 2)) = [] :=
    (off _ (below i)).trans (empty _)
  have injection : [incoming,bank src,bank 1,bank 2].Nodup := by
    have distinct := ((by decide : ([0,1,2] : List (Fin T)).Nodup).map bank.injective)
    exact List.nodup_cons.mpr ⟨by simp [(outside _).symm],distinct⟩
  obtain ⟨v',copyUser,load⟩ := bcopy_exec body injection v B (init 1) (init 2)
  rw [inputWord,init 0,List.append_nil] at load
  let C := {B with R := Function.update B.R (bank src) input}
  have loaded (i : Fin T) (ne : i ≠ src) : C.R (bank i) = B.R (bank i) :=
    Function.update_of_ne (bank.injective.ne ne) ..
  obtain ⟨y,D,t,yu,paid,run,_,read⟩ := directoryChartRoleSplit_exec (P := Empty) capacity (a*rows) H width V
    (Nat.mul_pos outer rowCount) labels row fits archive widths clean Empty.elim (embDn bank v') (embStk bank C)
    (fun i => (congrFun bl _).trans (left i)) (by change C.R (bank src) = input; simp [C])
    (fun i => (loaded _ (by intro eq; have h := congrArg Fin.val eq; change 1+i.val = 0 at h; omega)).trans (init _))
    (fun i => (loaded _ (below 0 i)).trans (hdr i))
  obtain ⟨z,k,same,time,normalize⟩ := read j
  obtain ⟨y',F,exec,_,kept,view,away⟩ := exec_emb (body' := body) (ι := Empty.elim) bank.injective
    (fun f => nomatch f) (Exec.seq run normalize) v' rfl C rfl
  have l := congrArg (fun Z : Stacks T prime => Z.L port) view
  have h := congrArg (fun Z : Stacks T prime => Z.R port) view
  refine ⟨y',F,_,kept.trans (same.trans (yu.trans (copyUser.trans user))),?_,Exec.seq (Exec.seq setup load) exec,?_,?_,?_⟩
  · have len : input.length = a*rows*142080*H*width := by
      dsimp only [input]
      rw [List.flatMap_def,BlockRotationData.uniform_volume width]
      · simp
      · intro xs hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        exact widths i (List.mem_range.mp hi)
    have cap := Nat.mul_le_mul_left (a*rows*142080*H) fits
    rw [len,Nat.add_mul]
    omega
  · simpa only [embStk,port,Function.comp_apply,Function.update_self] using l
  · simpa only [embStk,port,Function.comp_apply,Function.update_self] using h
  · intro i hi
    refine ⟨(away i hi).1.trans (congrFun bl i),(away i hi).2.trans ?_⟩
    change Function.update B.R (bank src) input i = _
    rw [Function.update_of_ne (hi _).symm,br]
    exact (Function.update_of_ne (hi _).symm ..).trans (Function.update_of_ne (hi _).symm ..)

private theorem metadata_queue_independent {w : ℕ} (W a rows H width : ℕ)
    (weights : Fin 64 → ZMod (prime^(w+1))) (input queue : List (Fin (prime+4)))
    (i : Fin 9) (other : i ≠ 8) :
    ordinaryEntryWords W a rows H true weights width input (ordinaryMetadataPorts i).val =
      ordinaryEntryWords W a rows H true weights width queue (ordinaryMetadataPorts i).val := by
  fin_cases i <;> first | rfl | contradiction

/-- Load a smaller chart after selecting its role. Eight metadata sources
remain on the caller. Only the archive source changes to the selected port. -/
theorem childRoleChartEntry_exec {N Q s k back w : ℕ} {P U : Type} (body : P → Pr P N Q prime U)
    (place : Fin (((s+5)+k)+back) ↪ Fin N) (room : 59 ≤ s)
    (splitPlace : Fin ((((1+142080)+2)+2)+12) ↪ Fin N)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (sources : Fin 9 → Fin N) (cut tmp aux : Fin N)
    (W a rows H width : ℕ) (role : Fin 142080) (archive : ℕ → List (Fin (prime+4)))
    (outer : 0 < a) (rowCount : 0 < rows) (labels : 0 < H) (positive : 0 < W)
    (fits : width ≤ (prime^(w+1))^128*W)
    (widths : ∀ i < a*rows*142080*H, (archive i).length = width)
    (clean : ∀ i < a*rows*142080*H, blank ∉ archive i) (u : HS N Q prime U) (S : Stacks N prime) :
    let V := (prime^(w+1))^128*W
    let T := ((1+142080)+2)+2
    let bank := (Fin.castAddEmb (n := T) 12).trans splitPlace
    let r := (roleSplitCountBank 142080).trans splitPlace
    let port := ((role.natAdd 1).castAdd 2).castAdd 2
    let select : Pr P N Q prime U := childRoleQueueProgram capacity splitPlace (sources 8) role
    let localBank := ((Fin.castAddEmb (n := s) 5).trans (Fin.castAddEmb k)).trans (Fin.castAddEmb back)
    let scanner := localBank.trans place
    let chart := ((Fin.natAddEmb (s+5) (m := k)).trans (Fin.castAddEmb back)).trans place
    let dst := (ordinaryMetadataPorts.trans (Fin.castLEEmb room)).trans scanner
    let saved := scanner ((40 : Fin 59).castLE room)
    let input := (List.range (a*rows*142080*H)).flatMap archive
    let queue := directoryChartQueue (some role) H 0 (a*rows*H) archive
    let weights := fun _ : Fin 64 => (1 : ZMod (prime^(w+1)))
    let words := directoryChartWords (S.R cut) W a rows H true weights width queue
    let source := Function.update sources 8 (bank port)
    let load : Pr P N Q prime U := (Record.copyLeafHeaders source dst tmp aux (List.finRange 9)).seq (bcopy cut saved tmp aux)
    (S.R cut).length ≤ a*rows*H*V →
    (∀ i, S.R (sources i) = ordinaryEntryWords W a rows H true weights width input (ordinaryMetadataPorts i).val) →
    (∀ j i, bank j ≠ sources i) → (∀ j i, bank j ≠ place i) →
    (∀ j, bank j ≠ cut ∧ bank j ≠ tmp ∧ bank j ≠ aux) →
    (∀ i j, source i ≠ dst j) → (∀ i, [source i,dst i,tmp,aux].Nodup) →
    (∀ i, cut ≠ dst i) → [cut,saved,tmp,aux].Nodup → S.R tmp = [] → S.R aux = [] →
    (∀ j : Fin (s+5), let i := place ((j.castAdd k).castAdd back); S.L i = [] ∧ S.R i = []) →
    (∀ j : Fin back, let i := place (j.natAdd ((s+5)+k)); S.L i = [] ∧ S.R i = []) →
    r 0 = sources 5 → r 1 = sources 3 → r 2 = sources 1 → r 3 = sources 2 →
    (∀ i : Fin 14, 4 ≤ i.val → S.R (r i) = []) →
    (∀ i, S.L (bank i) = []) → (∀ i, S.R (bank i) = []) →
    ∃ z F t, z.user = u.user ∧
      t ≤ (149*(T+5)+2417)*(a*rows*142080*H*V) ∧
      Exec body (select.seq load) (mk u S) t (mk z F) ∧
      ordinaryParentEntry (T := s) back words (embStk chart F) = embStk place F ∧
      (∀ i, F.L (chart i) = S.L (chart i) ∧ F.R (chart i) = S.R (chart i)) ∧
      ∀ j, (∀ i, bank i ≠ j) → (∀ i, scanner i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro V T bank r port select localBank scanner chart dst saved input queue weights words source load cutFits headers off chartOff work
    apart ports cutOff cutPorts tmpFree auxFree front backFree p₀ p₁ p₂ p₃ fresh splitLeft splitRight
  have row : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  obtain ⟨v,B,n,user,time,run,_,selected,frame⟩ := childRoleQueue_exec (w := w) body capacity splitPlace
    (sources 8) u S W a rows H width V outer rowCount labels row fits archive widths clean role
    (by rw [p₀]; exact headers 5) (by rw [p₁]; exact headers 3) (by rw [p₂]; exact headers 1) (by rw [p₃]; exact headers 2) fresh splitLeft
    (headers 8) (fun i => off i 8) splitRight
  have src (i : Fin 9) : B.R (source i) = ordinaryEntryWords W a rows H true weights width queue (ordinaryMetadataPorts i).val := by
    by_cases eq : i = 8
    · subst i
      change B.R (source 8) = queue
      rw [show source 8 = bank port from Function.update_self ..]
      exact selected
    rw [show source i = sources i from Function.update_of_ne eq ..,(frame _ (fun j => off j i)).2,headers]
    exact metadata_queue_independent W a rows H width weights input queue i eq
  have kept (i) := frame (place i) (fun j => chartOff j i)
  have read (i) (empty : S.L (place i) = [] ∧ S.R (place i) = []) :
      B.L (place i) = [] ∧ B.R (place i) = [] := ⟨(kept i).1.trans empty.1,(kept i).2.trans empty.2⟩
  obtain ⟨z,F,last,prepare,entry,left,right⟩ := directoryChartEntry_exec body place room source cut tmp aux
    W a rows H true weights width queue v B src apart ports cutOff cutPorts
    ((frame tmp (fun j => (work j).2.1)).2.trans tmpFree) ((frame aux (fun j => (work j).2.2)).2.trans auxFree)
    (fun j => read _ (front j)) (fun j => read _ (backFree j))
  have cutoff := (frame cut (fun j => (work j).1)).2
  rw [cutoff] at prepare entry
  simp only [ite_true,Nat.add_zero] at prepare
  refine ⟨z,F,_,last.trans user,?_,Exec.seq run prepare,entry,?_,?_⟩
  · have loading := directoryChartEntry_volume_le (w := w) (parents := 0) true (some role) archive (S.R cut)
      widths (Nat.zero_le _) positive outer rowCount labels fits cutFits
    change 6*(_+a+rows+H+w+width+W.size+0+queue.length)+55+(6*(S.R cut).length+6) ≤ 499*(a*rows*H*V) at loading
    simp only [Nat.add_zero] at loading
    have small : a*rows*H*V ≤ a*rows*142080*H*V := Nat.mul_le_mul_right V (Nat.mul_le_mul_right H (Nat.le_mul_of_pos_right (a*rows) (by decide : 0 < 142080)))
    have block : H*width ≤ a*rows*H*V :=
      (Nat.mul_le_mul_left H fits).trans (by rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos outer rowCount))
    have groups : a*rows ≤ a*rows*H*V :=
      (Nat.le_mul_of_pos_right _ labels).trans (Nat.le_mul_of_pos_right _ row)
    have pos := Nat.mul_pos outer rowCount
    change n ≤ 36*(H*width+a*rows)+52+(149*(T+5)+1794)*(a*rows*142080*H*V) at time
    rw [Nat.add_mul] at time ⊢
    omega
  · intro i
    refine ⟨(congrFun left _).trans (kept _).1,(right _ ?_).trans (kept _).2⟩
    intro j eq
    have bad := congrArg Fin.val (place.injective eq)
    change s+5+i.val = j.val at bad
    omega
  · intro j outside privateOff
    exact ⟨(congrFun left j).trans (frame j outside).1,(right j (fun i => (privateOff i).symm)).trans (frame j outside).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
