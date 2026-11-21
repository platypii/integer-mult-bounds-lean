module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryChildCost
public import IntegerMultBounds.MathlibTM2.M6.BitScheduledChildQueue
public import IntegerMultBounds.MathlibTM2.Cover.LabelCallerHeaders
public import IntegerMultBounds.MathlibTM2.Host.UnaryBinaryHalving
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderOrdinaryOwner
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderPiece

/-! Interpret the ordinary PR589 owner tapes at a common live label. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Matrix
open Shared50ModularControl (prime)
open IntegerMultBounds.Networks.Certificates.PR589.Nine
open Cover LabelTraversal FlatCoordinateLayout

open Stack Host

/-- Finish a nonroot scanner bank after the child queue transfer. The seven
header sources and two work registers can stay outside the caller/scan bank. -/
theorem childQueue_headers_exec {T Q w : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin (21+59) ↪ Fin T) (source : Fin 7 → Fin T) (tmp aux : Fin T)
    (W a b h width : ℕ) (parent : Fin 64 → ZMod (prime^(w+1))) (tail queue : List (Fin (prime+4)))
    (u v : HS T Q prime U) (S : Stacks T prime) (p : Pr P T Q prime U) (t : ℕ) :
    let scanner := (Fin.natAddEmb 21 (m := 59)).trans bank
    let dst := ordinaryHeaderPorts.trans scanner
    let words := ordinaryEntryWords W a b h false parent width queue
    let D : Stacks T prime := {S with R := (Function.update (Function.update (Function.update
      S.R (bank 7) tail) (scanner 58) queue) (scanner 47) (List.replicate width Node.tick))}
    Exec body p (mk u S) t (mk v D) → v.user = u.user →
    (∀ j, S.R (scanner j) = []) → (∀ i, S.R (source i) = words (ordinaryHeaderPorts i).val) →
    (∀ k ∈ tmp :: aux :: (List.finRange 7).map source, ∀ j, k ≠ bank j) →
    (∀ i, [source i,dst i,tmp,aux].Nodup) → S.R tmp = [] → S.R aux = [] →
    ∃ z F, z.user = u.user ∧ F.L = S.L ∧ (∀ j : Fin 59, F.R (scanner j) = words j.val) ∧
      Exec body (p.seq (Cover.Fallback.Record.copyLeafHeaders source dst tmp aux (List.finRange 7)))
        (mk u S) (t+(((List.finRange 7).map (fun i => 6*(words (ordinaryHeaderPorts i).val).length+6)).sum+1)) (mk z F) := by
  intro scanner dst words D prior same fresh sources outside ports temp auxFree
  have keep (k : Fin T) (hk : k ∈ tmp :: aux :: (List.finRange 7).map source) : D.R k = S.R k := by
    simp [D,scanner,Function.update_of_ne,outside k hk]
  have mem (i : Fin 7) : source i ∈ tmp :: aux :: (List.finRange 7).map source :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_finRange i)))
  obtain ⟨z,F,user,run,left,loaded,_⟩ := ordinaryHeaders_exec body source scanner (by decide) tmp aux
    W a b h false parent width queue v D (fun i => (keep _ (mem i)).trans (sources i))
    (fun i j => outside _ (mem i) _) ports ((keep _ (by simp)).trans temp)
    ((keep _ (by simp)).trans auxFree) (childQueue_scanner bank S tail queue width fresh)
  exact ⟨z,F,user.trans same,left,loaded,Exec.seq prior run⟩

/-- Normalize the caller's chart headers and decode the three row dimensions
and both spectator factors for the scanner. -/
theorem ordinaryDirectoryHeaders_exec {K T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 26 ↪ Fin T) (roles : Tapes K prime) (v : RecursiveInterchangeLayout.Descriptor) (w : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime) (headers : LabelCallerHeaders.Represents r S roles v w) :
    let dims : List (Fin 7) := [0,1,2,4,5]
    (∀ i ∈ dims, S.R (LabelDecode.target r i) = []) → (∀ k ∈ [r 9,r 10,r 11], S.R k = []) →
    ∃ z F t, Exec body ((LabelCallerHeaders.load r).seq (LabelDecode.program r dims)) (mk u S) t (mk z F) ∧
      z.user = u.user ∧ t ≤ LabelCallerHeaders.cost r S + 17*(v.beforeRows+v.rows+v.beforeH+v.between+v.afterD)+86 ∧
      (∀ i ∈ dims, F.R (LabelDecode.target r i) = List.replicate (LabelDecode.field v w i) (bitSymbol true)) ∧
      (∀ i, F.R (LabelDecode.source r i) = (FlatCoordinateSchedule.bits (LabelDecode.field v w i)).map bitSymbol ∧
        F.L (LabelDecode.source r i) = [separator]) ∧
      ∀ j, j ∉ LabelCallerHeaders.ports r → j ∉ dims.map (LabelDecode.target r) → F.R j = S.R j ∧ F.L j = S.L j := by
  intro dims fresh scratch
  obtain ⟨a,B,m,user,paid,binary,off,load⟩ := LabelCallerHeaders.load_exec body r roles v w u S headers
  have separate (j : Fin 26) (small : j.val < 19) : r j ∉ LabelCallerHeaders.ports r := by
    intro mem
    obtain ⟨i,_,eq⟩ := List.mem_map.mp mem
    have val := congrArg Fin.val (r.injective eq)
    change 19+i.val = j.val at val
    omega
  obtain ⟨z,R,n,keep,time,unary,others,decode⟩ := LabelDecode.runs body r (LabelDecode.field v w)
    dims (by decide) a B (fun i _ => (binary i).1)
    (fun i hi => (off _ (separate _ (by change i.val < 19; omega))).1.trans (fresh i hi))
    (by
      intro j hj
      have unchanged : B.R j = S.R j := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl <;> exact (off _ (separate _ (by decide))).1
      exact unchanged.trans (scratch j hj))
  refine ⟨z,_,m+n,Exec.seq load decode,keep.trans user,?_,unary,?_,?_⟩
  · change n ≤ 17*(v.beforeRows+1)+(17*(v.rows+1)+(17*(v.beforeH+1)+(17*(v.between+1)+(17*(v.afterD+1)+0))))+1 at time
    omega
  · intro i
    refine ⟨(others _ ?_).trans (binary i).1,(binary i).2⟩
    intro mem
    obtain ⟨j,_,eq⟩ := List.mem_map.mp mem
    have val := congrArg Fin.val (r.injective eq)
    change j.val = 19+i.val at val
    omega
  · intro j untouched unused
    exact ⟨(others j unused).trans (off j untouched).1,(off j untouched).2⟩

/-- From the normalized precision header, load the scanner's predecessor clock
on a fresh tape. Both the binary source and the scratch tapes are preserved. -/
theorem ordinaryClock_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    {src dst a b c : Fin T} (ports : [src,dst,a,b,c].Nodup) (w : ℕ)
    (u : HS T Q prime U) (S : Stacks T prime)
    (word : S.R src = (FlatCoordinateSchedule.bits (w+1)).map bitSymbol)
    (empty : ∀ j ∈ [dst,a,b,c], S.R j = []) :
    ∃ z n, z.user = u.user ∧ n ≤ 17*w+35 ∧
      Exec body ((toUnary src dst a b c).seq (.act (.pop (.rt dst) (fun v _ => v) .done)))
        (mk u S) n (mk z {S with R := Function.update S.R dst (List.replicate w (bitSymbol true))}) := by
  obtain ⟨z,t,user,paid,decode⟩ := LabelDecode.field_exec body ports (w+1) u S word empty
  let D : Stacks T prime := {S with R := Function.update S.R dst (List.replicate (w+1) (bitSymbol true))}
  have pop := Exec.act (body := body) (.pop (.rt dst) (fun v _ => v) .done) (mk z D)
  have endPop : (Action.pop (.rt dst) (fun v _ => v) .done : Act T Q prime U).run (mk z D) =
      mk z {S with R := Function.update S.R dst (List.replicate w (bitSymbol true))} := by
    simp [Action.run,update_rt,D,Function.update_idem]
  rw [endPop] at pop
  exact ⟨z,t+1,user,by omega,Exec.seq decode pop⟩

open Fallback in
/-- Copy and widen the root cutoff without changing its source or the tape
supplying the common binary precision. -/
theorem copyCutoff_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (src header cut cnt tmp scratch : Fin T) (cutoff L : ℕ) (fits : cutoff.size ≤ L)
    (u : HS T Q prime U) (S : Stacks T prime)
    (regs : [src,header,cut,cnt,tmp,scratch].Nodup) (word : S.R src = binSyms cutoff.size cutoff)
    (precision : (S.R header).length = L) (blankCut : S.R cut = []) (a : S.R cnt = [])
    (b : S.R tmp = []) (c : S.R scratch = []) :
    ∃ z, z.user = u.user ∧ Exec body ((bcopy src cut cnt tmp).seq (bwiden cut header cnt tmp scratch))
      (mk u S) (6*cutoff.size+12*L+24) (mk z {S with R := Function.update S.R cut (binSyms L cutoff)}) := by
  regs_ne regs
  obtain ⟨v,user,copy⟩ := bcopy_exec (body := body) (a := src) (c := cut) (t₁ := cnt) (t₂ := tmp)
    (by simp_all [ne_comm]) u S a b
  rw [word,length_binSyms,blankCut,List.append_nil] at copy
  let D : Stacks T prime := {S with R := Function.update S.R cut (binSyms cutoff.size cutoff)}
  obtain ⟨z,final,widen⟩ := bwiden_exec (body := body) (a := cut) (wR := header) (cnt := cnt)
    (t₁ := tmp) (t₂ := scratch) (by simp_all [ne_comm]) fits (Nat.lt_size_self cutoff) v D
    (by simp [D]) (by change (Function.update S.R cut _ header).length = L; rw [Function.update_of_ne (by assumption)]; exact precision)
    (by simp [D,Function.update_of_ne, *, Ne.symm])
    (by simp [D,Function.update_of_ne, *, Ne.symm])
    (by simp [D,Function.update_of_ne, *, Ne.symm])
  exact ⟨z,final.trans user,(Exec.seq copy widen).cast (by omega) (by simp [D])⟩

open Fallback in
/-- Copy the caller's cutoff to the dispatcher's last tape and pad it to the
root precision. The source headers survive and the column scratch is restored. -/
theorem ordinaryRootCutoff_exec [M8.Machine.Net] {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (placement : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (src header : Fin T)
    (root : RecursiveInterchangeLayout.Descriptor) (cutoff : ℕ) (within : cutoff ≤ root.width)
    (u : HS T Q prime U) (S : Stacks T prime) :
    let cut := placement (Fin.last _)
    let col := columnBank.trans placement
    let L := root.width.size
    [src,header,cut,col 0,col 1,col 3].Nodup →
    S.R src = binSyms cutoff.size cutoff → (S.R header).length = L →
    S.R cut = [] → S.R (col 0) = [] → S.R (col 1) = [] → S.R (col 3) = [] →
    ∃ z, z.user = u.user ∧
      Exec body ((bcopy src cut (col 0) (col 1)).seq (bwiden cut header (col 0) (col 1) (col 3)))
        (mk u S) (6*cutoff.size+12*L+24)
        (mk z {S with R := Function.update S.R cut (binSyms L cutoff)}) ∧
      cutoff < 2^L ∧ ∀ path : List (Fin nodeChildren5.length),
        (path.foldl (scheduledChild prime) root).width.size ≤ L := by
  intro cut col L regs word precision blankCut a b c
  obtain ⟨z,user,run⟩ := copyCutoff_exec body src header cut (col 0) (col 1) (col 3) cutoff L
    (Nat.size_le_size within) u S regs word precision blankCut a b c
  refine ⟨z,user,run,within.trans_lt (Nat.lt_size_self _),fun path => ?_⟩
  have bound := directoryDigits_bound prime root path
  apply Nat.size_le_size
  omega

/-- The shared root precision is short enough even at the last active parent:
writing the child's width and testing the cutoff together cost one volume term. -/
theorem ordinaryChildComparison_volume_le (root : RecursiveInterchangeLayout.Descriptor)
    (depth b cutoff rank w W : ℕ) (levels : 0 < depth) (base : 0 < b)
    (width : root.width = 64^depth*b) (stop : 42^depth*b ≤ cutoff)
    (active : cutoff ≤ 64*(w+1)) (fits : rank ≤ 64) (live : 0 < W) :
    let L := root.width.size
    let M := prime^(w+1)
    4*w+23*((w+1)*rank)+22*L+51 ≤ 2940*(M^128*W) := by
  intro L M
  have room := alignedRootWidth_le root depth b cutoff levels base width stop
  have pos : 0 < root.width := width ▸ Nat.mul_pos (by positivity) base
  have bits : L ≤ cutoff := Nat.size_le.mpr (by omega)
  have rankWidth := Nat.mul_le_mul_left (w+1) fits
  have atom : w+1 ≤ M := (Nat.lt_two_pow_self (n := w+1)).le.trans
    (Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _)
  have vol : w+1 ≤ M^128*W := atom.trans ((Nat.le_self_pow (by decide : 128 ≠ 0) M).trans
    (Nat.le_mul_of_pos_right _ live))
  omega

/-- Turn the parent's predecessor clock into the child's binary width. The
cutoff register sets the padding. Only the comparison operand survives. -/
theorem ordinaryChildWidth_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (rank w L : ℕ) (fits : ((w+1)*rank).size ≤ L)
    (u : HS T Q prime U) (S : Stacks T prime) (clock : (S.R (r 0)).length = w)
    (precision : (S.R (r 1)).length = L) (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) :
    let width := (w+1)*rank
    let push := Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)
    let pop := Prog.act (.pop (.rt (r 0)) (fun v _ => v) .done)
    ∃ z n, z.user = u.user ∧ n ≤ 4*w+23*width+12*L+40 ∧
      Exec body (((push.seq (Node.umul rank (r 0) (r 2) (r 4))).seq pop).seq
        ((unaryBinaryWidth (r 2) (r 1) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)).seq (bclear (r 2))))
        (mk u S) n (mk z {S with R := Function.update S.R (r 3) (binSyms L width)}) := by
  intro width push pop
  let A : Stacks T prime := {S with R := Function.update S.R (r 0) (Node.tick :: S.R (r 0))}
  have start : Exec body push (mk u S) 1 (mk u A) := by
    apply (Exec.act (body := body) (.push (.rt (r 0)) (fun _ => Node.tick) .done) (mk u S)).cast rfl
    simp [A,Action.run,update_rt]
  obtain ⟨v,user,multiply⟩ := Node.umul_exec (body := body) rank (a := r 0) (b := r 2) (t := r 4)
    (by simp) (by simp) (by simp) u A (by simpa [A] using empty 4 (by decide))
  have count : (A.R (r 0)).length = w+1 := by simp [A,clock]
  rw [count,show A.R (r 2) = [] by simpa [A] using empty 2 (by decide),List.append_nil,Nat.mul_comm rank] at multiply
  let B : Stacks T prime := {S with R := Function.update S.R (r 2) (List.replicate width Node.tick)}
  have restore : Exec body pop (mk v {A with R := Function.update A.R (r 2) (List.replicate width Node.tick)}) 1 (mk v B) := by
    apply (Exec.act (body := body) (.pop (.rt (r 0)) (fun v _ => v) .done : Act T Q prime U)
      (mk v {A with R := Function.update A.R (r 2) (List.replicate width Node.tick)})).cast rfl
    simp [Action.run,A,B,update_rt,Function.update_comm (show r 2 ≠ r 0 by simp)]
  have free (j : Fin 10) (hj : 3 ≤ j.val) : B.R (r j) = [] := by
    have ne : j ≠ 2 := fun eq => by subst j; contradiction
    simpa [B,Function.update_of_ne (r.injective.ne ne)] using empty j (by omega)
  obtain ⟨y,t,same,cost,binary⟩ := unaryBinaryWidth_exec (body := body) (src := r 2) (width := r 1) (dst := r 3)
    (a := r 4) (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9) (by simp)
    width L fits v B (by simp [B]) (by simpa [B] using precision) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact free _ (by decide))
  let D : Stacks T prime := {B with R := Function.update B.R (r 3) (binSyms L width)}
  obtain ⟨z,final,_,erase⟩ := bclear_exec (body := body) (r 2) y D
  have len : (D.R (r 2)).length = width := by simp [D,B]
  rw [len] at erase
  refine ⟨z,_,final.trans (same.trans user),?_,(Exec.seq (Exec.seq (Exec.seq start multiply) restore)
    (Exec.seq binary erase)).cast rfl ?_⟩
  · omega
  · have reset : Function.update S.R (r 2) [] = S.R := by
      rw [← empty 2 (by decide),Function.update_eq_self]
    simp [D,B,Function.update_comm (show r 3 ≠ r 2 by simp),reset]

/-- Compare from the live predecessor clock and restore the full stack bank
before either child branch starts. The comparison bit survives cleanup. -/
noncomputable def ordinaryCutoffTest {T Q : ℕ} {P U : Type} (r : Fin 10 ↪ Fin T) (rank : ℕ) : Pr P T Q prime U :=
  let push := Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)
  let pop := Prog.act (.pop (.rt (r 0)) (fun v _ => v) .done)
  let width := ((push.seq (Node.umul rank (r 0) (r 2) (r 4))).seq pop).seq
    ((unaryBinaryWidth (r 2) (r 1) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)).seq (bclear (r 2)))
  width.seq ((blt (r 1) (r 3) (r 4) (r 5) (r 6) (r 7)).seq (bclear (r 3)))

theorem ordinaryCutoffTest_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (rank w L cutoff : ℕ) (cutFits : cutoff < 2^L) (fits : ((w+1)*rank).size ≤ L)
    (u : HS T Q prime U) (S : Stacks T prime) (clock : (S.R (r 0)).length = w)
    (word : S.R (r 1) = binSyms L cutoff) (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) :
    ∃ z n, z.user = u.user ∧ z.scan (r 7) = bitSymbol (decide (cutoff < (w+1)*rank)) ∧
      n ≤ 4*w+23*((w+1)*rank)+22*L+50 ∧ Exec body (ordinaryCutoffTest r rank) (mk u S) n (mk z S) := by
  let width := (w+1)*rank
  obtain ⟨v,t,user,cost,prepare⟩ := ordinaryChildWidth_exec body r rank w L fits u S clock
    (word ▸ length_binSyms ..) empty
  let D : Stacks T prime := {S with R := Function.update S.R (r 3) (binSyms L width)}
  obtain ⟨y,same,flag,_,compare⟩ := blt_exec body (a := r 1) (b := r 3) (tx := r 4) (ty := r 5)
    (tz := r 6) (cy := r 7) (by simp) (by simp) (by simp) cutFits (Nat.size_le.mp fits) v D
    (by simpa [D] using word) (by simp [D,width]) (by simpa [D] using empty 4 (by decide))
    (by simpa [D] using empty 5 (by decide)) (by simpa [D] using empty 6 (by decide))
  obtain ⟨z,final,slots,erase⟩ := bclear_exec (body := body) (r 3) y D
  have len : (D.R (r 3)).length = L := by simp [D]
  rw [len] at erase
  have reset : Function.update S.R (r 3) [] = S.R := by rw [← empty 3 (by decide),Function.update_eq_self]
  refine ⟨z,_,final.trans (same.trans user),(congrFun slots _).trans flag,?_,(Exec.seq prepare
    (Exec.seq compare erase)).cast rfl ?_⟩
  · omega
  · simp [D,reset]

local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

def cutoffColumnSlots : Fin 10 ↪ Fin 35 := ⟨![33,34,0,1,3,4,5,6,7,8],by decide⟩

/-- Reuse the column clock and eight empty column registers. The persistent
cutoff lives outside the routing placement, so the packed call can read it. -/
def ordinaryCutoffPorts {T : ℕ} (bank : Fin 35 ↪ Fin T) (cut : Fin T)
    (off : ∀ i, bank i ≠ cut) : Fin 10 ↪ Fin T :=
  ⟨fun j => if j = 1 then cut else bank (cutoffColumnSlots j),by
    intro i j eq
    dsimp only at eq
    split_ifs at eq with hi hj hj
    · exact hi.trans hj.symm
    · exact (off _ eq.symm).elim
    · exact (off _ eq).elim
    · exact cutoffColumnSlots.injective (bank.injective eq)⟩

open Fallback RecursiveInterchangeLayout in
/-- The role-stream payload passed to an ordinary call is exactly one
scheduled occurrence's volume. This identifies its charge in parent units. -/
theorem ordinaryScheduledMeasures (node : Descriptor) (i : Fin nodeChildren5.length) (w : ℕ)
    (aligned : node.width = 64*(w+1)) (rows : 142080 ∣ node.rows) :
    let parent := role node 142080
    let r := nodeChildren5[i.val]
    let g := 64-r
    let packed := ordinaryChildDescriptor r g w (CopyChildLayout.spectators parent)
    let child := scheduledChild prime node i
    rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child ∧
      packed.width = child.width ∧ volume prime packed * 142080 = volume prime node := by
  intro parent r g packed child
  have rankLayout : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child := by
    simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
    rfl
  have size := Fintype.card_congr (ordinaryScheduledLayout parent r g w)
  simp only [Fintype.card_fin,rankLayout] at size
  refine ⟨rankLayout,?_,?_⟩
  · rw [← rankLayout]
    exact Nat.mul_comm ..
  · rw [show volume prime packed = volume prime child from size]
    exact (scheduledChild_measures prime node ⟨w+1,aligned⟩ rows i).2

open Fallback RecursiveInterchangeLayout in
private theorem ordinaryOccurrenceTranspose (parent : Descriptor) (r g w : ℕ) (child : Descriptor)
    (eqn : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child) :
    let packed := ordinaryChildDescriptor r g w (CopyChildLayout.spectators parent)
    let layout := (ordinaryScheduledLayout parent r g w).trans (finCongr (congrArg (volume prime) eqn))
    ∀ (word : Fin (volume prime child) → ZMod 2) k,
      Shared50RecursiveNodeRows.transpose (one_dvd packed.rows) (word ∘ layout) k =
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word (layout k) := by
  subst child
  exact ordinaryScheduledTranspose parent r g w

open Fallback RecursiveInterchangeLayout in
/-- Read the predecessor clock and compare the child width with the cutoff. Equality executes the stopped exchange. -/
theorem ordinaryChildDispatch_exec [M8.Machine.Net] {P U : Type} {T : ℕ}
    (placement : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T) (body : P → Pr P T columnCapacity prime U) :
    let ports := columnPorts.trans placement
    let cut := placement (Fin.last _)
    let outside : ∀ i, ports i ≠ cut := fun i => placement.injective.ne (Fin.castSucc_ne_last i)
    ∃ C : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) w (aligned : node.width = 64*(w+1)),
      let r := nodeChildren5[i.val]
      let g := 64-r
      let parent := role node 142080
      let W := CopyChildLayout.spectators parent
      0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let is := ordinaryChildPackSchedule r g
      let routeTime := (is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let cmp := ordinaryCutoffPorts bank cut (fun i => outside _)
      let pass := fun js => statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule d js)
      let clean := fun (S : Stacks T prime) => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → S.L (ports k) = [] ∧ S.R (ports k) = []
      ∀ (v : HS T columnCapacity prime U) (S : Stacks T prime)
        (record : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
        (original : Fin (M^d*W) → ZMod 2)
        (input : (Fin d → ZMod M) → IntegerMultBounds.Swap.Shear.State (Fin (r+g)) (ZMod M))
        (f : P) (budget cutoff L : ℕ),
      let saved := fun D : Stacks T prime => ∀ j, (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j
      let desc := ordinaryChildDescriptor r g w W
      let child := scheduledChild prime node i
      let same : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child := by
        simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
        rfl
      let layout := (ordinaryScheduledLayout parent r g w).trans (finCongr (congrArg (volume prime) same))
      let onTape := fun (word : Fin (volume prime child) → ZMod 2) (D : Stacks T prime) =>
        ∀ z, readAt blank (D.L (bank 24)) (D.R (bank 24)) z =
          M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := desc) (word ∘ layout) z
      let columns := ColumnRecordReady bank M.size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q
      cutoff < 2^L → desc.width.size ≤ L →
      S.R cut = binSyms L cutoff →
      (cutoff < desc.width → child.width < node.width → ∀ word u D, onTape word D → clean D → saved D → D.R cut = binSyms L cutoff → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body (body f) (mk u D) t (mk y G) ∧
        onTape (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word) G ∧
        (∀ j : Fin 35, j ≠ 24 → G.L (bank j) = D.L (bank j) ∧ G.R (bank j) = D.R (bank j)) ∧ clean G ∧ saved G) →
      columns original (fun x => Fin.append (input x).1 (input x).2) S → clean S → ∃ z F n, z.user = v.user ∧
        n ≤ 4*w+23*desc.width+22*L+51+(if cutoff < desc.width then budget+2+2*(1+routeTime) else C*(desc.width*(M^d*W))) ∧
        Exec body (.seq (ordinaryCutoffTest cmp r)
          (.cond (fun u => symBit (u.scan (cmp 7))) (.seq (pass is) (.seq (.call f) (pass is.reverse)))
            (pass (stoppedParentSchedule r g)))) (mk v S) n (mk z F) ∧
        columns original (fun x => let t := Cover.Weighted.child r (fun _ => 1) (fun _ => 1) (input x)
                                   Fin.append t.1 t.2) F ∧ clean F ∧ saved F ∧ F.R cut = binSyms L cutoff ∧
        ∀ c, Fast.Main.mnProgPush (pass is) ≤ c → Fast.Main.mnProgPush (pass is.reverse) ≤ c →
          Fast.Main.mnProgPush (pass (stoppedParentSchedule r g)) ≤ c →
          (∀ f, Fast.Main.mnProgPush (body f) ≤ c) → StackGrowthExcept (bank 24) S F
            (c*(if cutoff < desc.width then 2*(1+routeTime) else C*(desc.width*(M^d*W)))) := by
  intro ports cut outside
  obtain ⟨C,stopped⟩ := stoppedOrdinaryChild_exec ports body
  refine ⟨C,?_⟩
  intro node i w aligned r g parent W hW d M is routeTime bank cmp pass clean v S record dest q original input f budget cutoff L
    saved desc child eqn layout onTape columns cutFits widthFits cutWord recurse start free
  have rankPos : 0 < r := (nodeChildren5_bounds i).1
  have rankBound : r ≤ 42 := nodeChildren5_le i
  have split : r+g = 64 := by dsimp only [g]; omega
  have gap : 0 < g := by omega
  have div : node.width/64 = w+1 := by simp [aligned]
  obtain ⟨u,m,user,flag,testCost,compare⟩ := ordinaryCutoffTest_exec body cmp r w L cutoff cutFits widthFits
    v S (by exact start.choose_spec.1.clock) (by exact cutWord) (by
      intro j hj
      have ne : j ≠ 1 := fun eq => by subst j; contradiction
      have scratch : ∀ k : Fin 10, 2 ≤ k.val → cutoffColumnSlots k ∈ shearWork := by decide
      simpa [cmp,ordinaryCutoffPorts,ne] using (start.choose_spec.1.scratch _ (scratch j hj)).2)
  change u.scan (cmp 7) = bitSymbol (decide (cutoff < desc.width)) at flag
  change m ≤ 4*w+23*desc.width+22*L+50 at testCost
  by_cases active : cutoff < desc.width
  · obtain ⟨z,F,n,hu,cost,run,done,clear,kept,growth⟩ := ordinaryChildRoute_exec ports body r g gap w W hW
      u S record dest q original input f budget (by
        intro smaller word y D reads clear saved
        let x := word ∘ layout.symm
        have entry : x ∘ layout = word := by funext k; simp [x]
        have less : child.width < node.width := by
          change r*(node.width/64) < node.width
          rw [div,aligned,← split,Nat.mul_comm r]
          exact smaller
        obtain ⟨v,G,t,user,time,run,returned,keep,empty,frame⟩ := recurse active less x y D
          (by simpa only [onTape,entry] using reads) clear saved ((saved cut outside).2.trans cutWord)
        refine ⟨v,G,t,user,time,run,?_,keep,empty,frame⟩
        have output : Shared50RecursiveNodeRows.transpose (one_dvd desc.rows) word =
            Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x ∘ layout := by
          funext k
          rw [← entry]
          exact ordinaryOccurrenceTranspose parent r g w child eqn x k
        intro k
        rw [output]
        exact returned k) start free
    refine ⟨z,F,_,hu.trans user,?_,Exec.seq compare (Exec.cond_true (by simp [mk_var,flag,active]) run),done,clear,kept,(kept cut outside).2.trans cutWord,?_⟩
    · rw [ite_eq_left active]
      change n ≤ budget+2+2*(1+routeTime) at cost
      omega
    · simpa only [ite_eq_left active] using fun c enter exit _ hb => growth c enter exit hb
  · obtain ⟨z,F,n,hu,cost,run,done,clear,kept⟩ := stopped r g split rankPos w W hW u S record dest q original input start free
    refine ⟨z,F,_,hu.trans user,?_,Exec.seq compare (Exec.cond_false (by simp [mk_var,flag,active]) run),done,clear,kept,(kept cut outside).2.trans cutWord,?_⟩
    · rw [ite_eq_right active]
      change n ≤ C*(desc.width*(M^d*W)) at cost
      omega
    · intro c _ _ hp hb j ne
      rw [ite_eq_right active]
      obtain ⟨l,r⟩ := StackGrowthExcept.of_exec (bank 24) run hp hb j ne
      have paid := Nat.mul_le_mul_left c cost
      exact ⟨l.trans (Nat.add_le_add_left paid _),r.trans (Nat.add_le_add_left paid _)⟩

/-- Multiply the decoded spectator factors and encode their product in the
minimal binary width expected on scanner tape 53. -/
theorem ordinarySpectatorWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 10 ↪ Fin T) (u : HS T Q prime U) (S : Stacks T prime) (between afterD : ℕ)
    (left : (S.R (r 0)).length = between) (right : (S.R (r 1)).length = afterD)
    (positive : 0 < afterD) (empty : ∀ j : Fin 10, 2 ≤ j.val → S.R (r j) = []) :
    let W := between*afterD
    ∃ z t, z.user = u.user ∧ t ≤ 34*W+14 ∧
      Exec body ((Mult.ShortConv.unaryProduct (r 0) (r 1) (r 2) (r 4) (r 5)).seq
        (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)))
        (mk u S) t (mk z {S with R := Function.update (Function.update S.R (r 2)
          (List.replicate W Node.tick)) (r 3) (binSyms W.size W)}) := by
  intro W
  obtain ⟨a,m,user,paid,product⟩ := Mult.ShortConv.unaryProduct_exec (body := body)
    (a := r 0) (b := r 1) (dst := r 2) (t₁ := r 4) (t₂ := r 5) (by simp) u S
    (empty 4 (by decide)) (empty 5 (by decide))
  rw [left,right,empty 2 (by decide),List.append_nil] at product
  let D : Stacks T prime := {S with R := Function.update S.R (r 2) (List.replicate W Node.tick)}
  have free (j : Fin 10) (hj : 3 ≤ j.val) : D.R (r j) = [] := by
    have ne : j ≠ 2 := fun eq => by subst j; exact (by decide : ¬3 ≤ (2 : Fin 10).val) hj
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),empty j (by omega)]
  obtain ⟨z,n,keep,bill,binary⟩ := unaryBinary_exec (body := body) (src := r 2) (dst := r 3) (a := r 4)
    (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9) (by simp) W a D
    (by simp [D]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact free _ (by decide))
  refine ⟨z,m+n,keep.trans user,?_,Exec.seq product binary⟩
  rw [left,right,show between*(4*afterD+9)+4 = 4*(between*afterD)+9*between+4 by ring] at paid
  have le : between ≤ W := Nat.le_mul_of_pos_right _ positive
  dsimp only [W] at *
  omega

/-- Compute the scanner's binary spectator product directly from the two
binary descriptor fields on a recursive call. -/
theorem directorySpectatorWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (ports : Fin 12 ↪ Fin T) (u : HS T Q prime U) (S : Stacks T prime) (b d : ℕ)
    (hb : 0 < b) (hd : 0 < d)
    (between : S.R (ports 10) = (FlatCoordinateSchedule.bits b).map bitSymbol)
    (afterD : S.R (ports 11) = (FlatCoordinateSchedule.bits d).map bitSymbol)
    (empty : ∀ i : Fin 10, S.R (ports (i.castAdd 2)) = []) :
    let r := (Fin.castAddEmb (n := 10) 2).trans ports
    let W := b*d
    let decoded := Function.update (Function.update S.R (r 0) (List.replicate b Node.tick))
      (r 1) (List.replicate d Node.tick)
    ∃ z t, z.user = u.user ∧ t ≤ 68*W+48 ∧
      Exec body (((toUnary (ports 10) (r 0) (r 4) (r 5) (r 6)).seq
        (toUnary (ports 11) (r 1) (r 4) (r 5) (r 6))).seq
        ((Mult.ShortConv.unaryProduct (r 0) (r 1) (r 2) (r 4) (r 5)).seq
        (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9))))
        (mk u S) t (mk z {S with R := Function.update (Function.update decoded (r 2)
          (List.replicate W Node.tick)) (r 3) (binSyms W.size W)}) := by
  intro r W decoded
  obtain ⟨v,m,vu,readB,first⟩ := LabelDecode.field_exec body
    ((by decide : ([10,0,4,5,6] : List (Fin 12)).Nodup).map ports.injective) b u S between (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> first | exact empty 0 | exact empty 4 | exact empty 5 | exact empty 6)
  let B := {S with R := Function.update S.R (r 0) (List.replicate b Node.tick)}
  have free (i : Fin 10) (hi : i ≠ 0) : B.R (r i) = [] :=
    (Function.update_of_ne (r.injective.ne hi) ..).trans (empty i)
  obtain ⟨y,n,yv,readD,second⟩ := LabelDecode.field_exec body
    ((by decide : ([11,1,4,5,6] : List (Fin 12)).Nodup).map ports.injective) d v B
    ((Function.update_of_ne (ports.injective.ne (by decide : (11 : Fin 12) ≠ 0)) ..).trans afterD) (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> first
        | exact free 1 (by decide) | exact free 4 (by decide) | exact free 5 (by decide) | exact free 6 (by decide))
  let D := {S with R := decoded}
  obtain ⟨z,k,zy,paid,run⟩ := ordinarySpectatorWord_exec body r y D b d
    (by simp [D,decoded]) (by simp [D,decoded]) hd (by
      intro i hi
      have h₁ : i ≠ 1 := fun eq => by subst i; contradiction
      have h₀ : i ≠ 0 := fun eq => by subst i; contradiction
      exact (Function.update_of_ne (r.injective.ne h₁) ..).trans (free i h₀))
  have lb : b ≤ W := Nat.le_mul_of_pos_right _ hd
  have ld : d ≤ W := Nat.le_mul_of_pos_left _ hb
  exact ⟨z,_,zy.trans (yv.trans vu),by change k ≤ 34*W+14 at paid; omega,Exec.seq (Exec.seq first second) run⟩

/-- Generate the scanner modulus from the normalized binary precision header.
The program writes its own unit seed before exponentiation. -/
theorem ordinaryModulusWord_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (r : Fin 11 ↪ Fin T) (u : HS T Q prime U) (initial : Stacks T prime) (w : ℕ)
    (precision : initial.R (r 10) = (FlatCoordinateSchedule.bits (w+1)).map bitSymbol)
    (fresh : ∀ j : Fin 11, j.val ≤ 9 → initial.R (r j) = []) :
    let M := prime^(w+1)
    ∃ z n, z.user = u.user ∧ n ≤ 60*M+28 ∧
      let S : Stacks T prime := {initial with R := Function.update initial.R (r 0) [Node.tick]}
      Exec body ((Prog.act (.push (.rt (r 0)) (fun _ => Node.tick) .done)).seq ((toUnary (r 10) (r 1) (r 4) (r 5) (r 6)).seq
        ((Node.expProg 0 prime (r 0) (r 1) (r 2) (r 4) (r 5) (r 6)).seq
        (unaryBinary (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8) (r 9)))))
        (mk u initial) n (mk z {S with R := Function.update (Function.update (Function.update S.R
          (r 1) (List.replicate (w+1) Node.tick)) (r 2) (List.replicate M Node.tick)) (r 3) (binSyms M.size M)}) := by
  intro M
  let S : Stacks T prime := {initial with R := Function.update initial.R (r 0) [Node.tick]}
  have seed := Exec.act (body := body) (.push (.rt (r 0)) (fun _ => Node.tick) .done) (mk u initial)
  have start : (Action.push (.rt (r 0)) (fun _ => Node.tick) .done : Act T Q prime U).run (mk u initial) =
      mk u S := by simp [Action.run,update_rt,S,fresh 0 (by decide)]
  rw [start] at seed
  have one : (S.R (r 0)).length = 1 := by simp [S]
  have empty (j : Fin 11) (lo : 1 ≤ j.val) (hi : j.val ≤ 9) : S.R (r j) = [] := by
    have ne : j ≠ 0 := fun eq => by subst j; exact (by decide : ¬1 ≤ (0 : Fin 11).val) lo
    exact (Function.update_of_ne (r.injective.ne ne) ..).trans (fresh j hi)
  obtain ⟨a,t,keep,price,decode⟩ := LabelDecode.field_exec body (src := r 10) (dst := r 1)
    (a := r 4) (b := r 5) (c := r 6) (by simp) (w+1) u S (by simpa [S] using precision) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact empty _ (by decide) (by decide))
  let D : Stacks T prime := {S with R := Function.update S.R (r 1) (List.replicate (w+1) Node.tick)}
  have free (j : Fin 11) (lo : 2 ≤ j.val) (hi : j.val ≤ 9) : D.R (r j) = [] := by
    have ne : j ≠ 1 := fun eq => by subst j; exact (by decide : ¬2 ≤ (1 : Fin 11).val) lo
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),empty j (by omega) hi]
  obtain ⟨b,m,user,paid,power⟩ := LabelCounts.power_exec body (one := r 0) (exponent := r 1)
    (dst := r 2) (t₁ := r 4) (t₂ := r 5) (t₃ := r 6) (by simp) a D (by simpa [D] using one) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> exact free _ (by decide) (by decide))
  have exponent : (D.R (r 1)).length = w+1 := by simp [D]
  rw [exponent] at paid power
  let B : Stacks T prime := {D with R := Function.update D.R (r 2) (List.replicate M Node.tick)}
  have blank (j : Fin 11) (lo : 3 ≤ j.val) (hi : j.val ≤ 9) : B.R (r j) = [] := by
    have ne : j ≠ 2 := fun eq => by subst j; exact (by decide : ¬3 ≤ (2 : Fin 11).val) lo
    change Function.update _ _ _ (r j) = _
    rw [Function.update_of_ne (r.injective.ne ne),free j (by omega) hi]
  obtain ⟨z,l,last,bill,binary⟩ := unaryBinary_exec (body := body) (src := r 2) (dst := r 3) (a := r 4)
    (h := r 5) (par := r 6) (bits := r 7) (cnt := r 8) (saved := r 9) (by simp) M b B
    (by simp [B]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact blank _ (by decide) (by decide))
  refine ⟨z,1+(t+(m+l)),last.trans (user.trans keep),?_,Exec.seq seed (Exec.seq decode (Exec.seq power binary))⟩
  have size : w+1 ≤ M := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le
  change m ≤ 22*M at paid
  omega

/-- Place each local owner program on the same permanent owners and a
disjoint private bank, even when its local owner slots are scattered. -/
noncomputable def idlePassBank {owners n : ℕ} (width : Fin n → ℕ) (k : Fin n)
    (slots : Fin owners ↪ Fin (width k)) :=
  (returnChartBank slots (Function.Embedding.refl _)).trans (Fallback.Record.exchangeBank owners width k)

theorem idlePassBank_owner {owners n : ℕ} (width : Fin n → ℕ) (k : Fin n)
    (slots : Fin owners ↪ Fin (width k)) (i : Fin owners) :
    idlePassBank width k slots (slots i) = i.castAdd _ := by
  unfold idlePassBank
  rw [Function.Embedding.trans_apply,returnChartBank_selected,Fallback.Record.exchangeBank_shared]
  rfl

/-- Assemble the initial stacks, storing the common owners once. Unused
positions in the occurrence banks start blank. -/
noncomputable def idlePassStacks {owners n : ℕ} (width : Fin n → ℕ)
    (slots : ∀ k, Fin owners ↪ Fin (width k)) (shared : Stacks owners prime)
    (entry : ∀ k, Stacks (width k) prime) :
    Stacks (owners + Fintype.card (Σ j, Fin (width j))) prime := by
  let decode := (Fintype.equivFin (Σ j, Fin (width j))).symm
  classical
  let bank (common : Fin owners → List (Fin (prime+4))) (words : ∀ j, Fin (width j) → List (Fin (prime+4))) :
      Fin (owners + Fintype.card (Σ j, Fin (width j))) → List (Fin (prime+4)) :=
    Fin.addCases common fun i =>
      let a := decode i
      if ∃ t, slots a.1 t = a.2 then [] else words a.1 a.2
  exact ⟨shared.inp,shared.out,bank shared.L (fun j => (entry j).L),bank shared.R (fun j => (entry j).R)⟩

theorem idlePassStacks_view {owners n : ℕ} (width : Fin n → ℕ)
    (slots : ∀ k, Fin owners ↪ Fin (width k)) (shared : Stacks owners prime)
    (entry : ∀ k, Stacks (width k) prime) (k : Fin n)
    (common : embStk (slots k) (entry k) = shared) :
    embStk (idlePassBank width k (slots k)) (idlePassStacks width slots shared entry) = entry k := by
  subst shared
  apply Stacks.ext
  · rfl
  · rfl
  all_goals
    funext j
    by_cases used : ∃ i, slots k i = j
    · obtain ⟨i,rfl⟩ := used
      simp [embStk,Function.comp_apply,idlePassBank_owner,idlePassStacks]
    · have place : idlePassBank width k (slots k) j =
          Fin.natAdd owners (Fallback.Record.exchangeScratch width k j) := by
        unfold idlePassBank
        rw [Function.Embedding.trans_apply,returnChartBank_private _ _ j (fun i h => used ⟨i,h⟩),
          Fallback.Record.exchangeBank_private]
      have decode : (Fintype.equivFin (Σ a, Fin (width a))).symm (Fallback.Record.exchangeScratch width k j) =
          ⟨k,j⟩ := (Fintype.equivFin (Σ a, Fin (width a))).symm_apply_apply ⟨k,j⟩
      simp only [embStk,Function.comp_apply,place,idlePassStacks,Fin.addCases_right]
      rw [decode]
      simp [used]

/-- All local control states fit the maximum over the finite occurrence list. -/
theorem idlePass_fits {n : ℕ} (states : Fin n → ℕ) (k : Fin n) :
    states k ≤ Finset.univ.sup states := Finset.le_sup (Finset.mem_univ k)

/-- Recursive calls carry their occurrence index in the common procedure table. -/
noncomputable def idlePassBody {owners n : ℕ} {P U : Type} (width states : Fin n → ℕ)
    (positive : ∀ k, 0 < states k) (slots : ∀ k, Fin owners ↪ Fin (width k))
    (body : ∀ k, P → Pr P (width k) (states k) prime U) (f : Fin n × P) :
    Pr (Fin n × P) (owners + Fintype.card (Σ j, Fin (width j))) (Finset.univ.sup states) prime U :=
  statePlacedPr (idlePassBank width f.1 (slots f.1)) (idlePass_fits states f.1) (positive f.1)
    (Prod.mk f.1) (body f.1 f.2)

/-- One normalization step installs the local control state. The resulting run
preserves both stacks of every other occurrence's private tapes. -/
theorem idlePassBank_exec {owners n : ℕ} {P U : Type} (width states : Fin n → ℕ) (k : Fin n)
    (positive : ∀ j, 0 < states j) (slots : ∀ j, Fin owners ↪ Fin (width j))
    (body : ∀ j, P → Pr P (width j) (states j) prime U)
    (p : Pr P (width k) (states k) prime U) (v : HS _ (Finset.univ.sup states) prime U) (S : Stacks _ prime)
    (z : HS (width k) (states k) prime U) (D : Stacks (width k) prime) (t : ℕ) :
    let bank := idlePassBank width k (slots k)
    Exec (body k) p (mk (stateLiftDown (positive k) (embDn bank v)) (embStk bank S)) t (mk z D) →
    ∃ u F, Exec (idlePassBody width states positive slots body)
      (statePlacedNormalized bank (idlePass_fits states k) (positive k) (Prod.mk k) p)
      (mk v S) (1+t) (mk u F) ∧ u.user = z.user ∧ embStk bank F = D ∧
      ∀ j, j ≠ k → ∀ a : Fin (width j),
        let h := Fin.natAdd owners (Fallback.Record.exchangeScratch width j a)
        F.L h = S.L h ∧ F.R h = S.R h := by
  intro bank run
  obtain ⟨u,_,user,exec⟩ := statePlaced_exec_normalized bank bank.injective (idlePass_fits states k)
    (positive k) (Prod.mk k) (body' := idlePassBody width states positive slots body) (fun _ => rfl) v S run
  refine ⟨u,_,exec,user,embStk_ovr bank.injective _ _,fun j ne a => embOvr_off _ _ (fun b => ?_)⟩
  exact Fallback.Record.exchangeBank_avoids owners width (Ne.symm ne) _ a

/-- Sequence the physical passes on the idle's distinct owners. Each pass may
return a different representation of the tape bank and has its own time bound. -/
theorem idleCopies_exec {T Q : ℕ} {P U α : Type} (i : Fin 9)
    (body : P → Pr P T Q prime U) (program : (Fin 32 × Fin 5) × Fin 222 → Pr P T Q prime U)
    (budget : (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (prepared : (Fin 32 × Fin 5) × Fin 222 → Stacks T prime → Prop)
    (ready : (Fin 142081 → α) → Stacks T prime → Prop)
    (effect : (Fin 32 × Fin 5) × Fin 222 → α → α → Prop)
    (pass : ∀ k x S (u : HS T Q prime U), ready x S → prepared k S →
      ∃ y D z n, Exec body (program k) (mk u S) n (mk z D) ∧ (n : ℝ) ≤ budget k ∧
        z.user = u.user ∧ ready y D ∧ (∀ a, a ≠ k → prepared a S → prepared a D) ∧
        effect k (x (idleTape i k)) (y (idleTape i k)) ∧
        ∀ j, j ≠ idleTape i k → y j = x j)
    (x : Fin 142081 → α) (S : Stacks T prime) (u : HS T Q prime U) (input : ready x S) (frames : ∀ k, prepared k S) :
    ∃ y D z n, Exec body (Prog.seqList (idleCopies.map program)) (mk u S) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
      (∀ k, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j := by
  have run (ks : List ((Fin 32 × Fin 5) × Fin 222)) (distinct : ks.Nodup)
      (x : Fin 142081 → α) (S : Stacks T prime) (u : HS T Q prime U) (input : ready x S) (frames : ∀ k ∈ ks, prepared k S) :
      ∃ y D z n, Exec body (Prog.seqList (ks.map program)) (mk u S) n (mk z D) ∧
        (n : ℝ) ≤ (ks.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
        (∀ k ∈ ks, effect k (x (idleTape i k)) (y (idleTape i k))) ∧
        ∀ j, (∀ k ∈ ks, j ≠ idleTape i k) → y j = x j := by
    induction ks generalizing x S u with
    | nil =>
      exact ⟨x,S,u,1,Exec.act .done _,by simp,rfl,input,by simp,fun _ _ => rfl⟩
    | cons k ks ih =>
      obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
      obtain ⟨v,B,t,m,firstRun,paid,keep,next,preserve,acted,off⟩ := pass k x S u input (frames k List.mem_cons_self)
      obtain ⟨y,D,z,n,rest,bill,user,final,acts,kept⟩ := ih tail v B t next
        (fun a ha => preserve a (fun h => fresh (h ▸ ha)) (frames a (List.mem_cons_of_mem _ ha)))
      refine ⟨y,D,z,m+n,Exec.seq firstRun rest,?_,user.trans keep,final,?_,?_⟩
      · simp only [List.map_cons,List.sum_cons,Nat.cast_add]
        linarith
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | member
        · rw [kept (idleTape i j) (fun a ha => (idleTape_injective i).ne (fun h => fresh (h.symm ▸ ha)))]
          exact acted
        · rw [← off _ ((idleTape_injective i).ne (fun h => fresh (h ▸ member)))]
          exact acts j member
      · intro j outside
        exact (kept j (fun a ha => outside a (List.mem_cons_of_mem _ ha))).trans
          (off j (outside k List.mem_cons_self))
  obtain ⟨y,D,z,n,exec,paid,user,final,acts,kept⟩ := run idleCopies
    (stageRuns_nodup.product (List.nodup_finRange _)) x S u input (fun k _ => frames k)
  refine ⟨y,D,z,n,exec,paid,user,final,fun k => acts k ?_,fun j h => kept j (fun a _ => h a)⟩
  exact List.mem_flatMap.mpr ⟨k.1,mem_stageRuns _,List.mem_map.mpr ⟨k.2,List.mem_finRange _,rfl⟩⟩

/-- Physical cell of a rational address in the fixed block, label and spectator slice. -/
noncomputable def ordinaryRoleAddress {w R W parents : ℕ} (parent : Fin 64 → ZMod (prime^(w+1)))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1))
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W) :
    (Axis ⊕ Axis → ℚ) → Fin (R*((prime^(w+1))^128*W)) :=
    let M := prime^(w+1)
    letI : NeZero M := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩
    let axes := Equiv.sumCongr stageAxis.symm stageAxis.symm
    let frame := fromBlocks (diagonal parent*g) 0 0 (M8.ReversedExchange.rev 64*g)
    let row : Fin R := (finProdFinEquiv (block,LabelAddress.address g)).cast count
    let pack := fun x => finProdFinEquiv (row,index ((frame.mulVec (x ∘ axes)) ∘ finSumFinEquiv.symm) spectator)
    pack ∘ addressMod M

/-- All selected owners realize the compiled idle at the same packed address
for each live label, inherited block and spectator. -/
theorem ordinaryIdle_read {w R W parents : ℕ} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (block : Fin parents) (g : LabelPadding.Label 64 (w+1)) (live : IsUnit g)
    (count : parents*(prime^(w+1))^(64*64) = R) (spectator : Fin W)
    (before after : Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2)
    (reads : ∀ k, OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val)
      (before (idleTape i k)) (after (idleTape i k)))
    (off : ∀ j, (∀ k, j ≠ idleTape i k) → after j = before j) :
    let address := ordinaryRoleAddress parent block g count spectator
    readRoles address after = (Piece.remainder i.val).run (readRoles address before) := by
  dsimp only [ordinaryRoleAddress]
  apply idleCopies_modular_read (w+1) i _ before after _ off
  intro k e P x
  rw [idleExchange_axes _ (port_checked _ (idleRole i k).port.isLt) e.1 e.2]
  exact (reads k).exchange units block g live count (x ∘ Equiv.sumCongr stageAxis.symm stageAxis.symm) spectator

/-- Run the installed passes on their common bank and read the compiled idle
from the very same final store and summed step bound. -/
theorem ordinaryIdle_exec {w R W parents T Q : ℕ} {P U : Type} (i : Fin 9)
    (parent : Fin 64 → ZMod (prime^(w+1))) (units : ∀ j, IsUnit (parent j))
    (count : parents*(prime^(w+1))^(64*64) = R)
    (body : P → Pr P T Q prime U) (program : (Fin 32 × Fin 5) × Fin 222 → Pr P T Q prime U)
    (budget : (Fin 32 × Fin 5) × Fin 222 → ℝ)
    (prepared : (Fin 32 × Fin 5) × Fin 222 → Stacks T prime → Prop)
    (ready : (Fin 142081 → Fin (R*((prime^(w+1))^128*W)) → ZMod 2) → Stacks T prime → Prop)
    (pass : ∀ k x S (u : HS T Q prime U), ready x S → prepared k S →
      ∃ y D z n, Exec body (program k) (mk u S) n (mk z D) ∧ (n : ℝ) ≤ budget k ∧
        z.user = u.user ∧ ready y D ∧ (∀ a, a ≠ k → prepared a S → prepared a D) ∧
        OriginalPortReads R W parents (idleInterval i k.2) parent
          (port (idleRole i k).port.val) (x (idleTape i k)) (y (idleTape i k)) ∧
        ∀ j, j ≠ idleTape i k → y j = x j)
    (x S u) (input : ready x S) (frames : ∀ k, prepared k S) :
    ∃ y D z n, Exec body (Prog.seqList (idleCopies.map program)) (mk u S) n (mk z D) ∧
      (n : ℝ) ≤ (idleCopies.map budget).sum + 1 ∧ z.user = u.user ∧ ready y D ∧
      (∀ j, (∀ k, j ≠ idleTape i k) → y j = x j) ∧
      ∀ block g, IsUnit g → ∀ spectator, let address := ordinaryRoleAddress parent block g count spectator
        readRoles address y = (Piece.remainder i.val).run (readRoles address x) := by
  obtain ⟨y,D,z,n,exec,paid,user,final,acts,kept⟩ := idleCopies_exec i body program budget prepared ready
    (fun k => OriginalPortReads R W parents (idleInterval i k.2) parent (port (idleRole i k).port.val))
    pass x S u input frames
  exact ⟨y,D,z,n,exec,paid,user,final,kept,fun block g live spectator =>
    ordinaryIdle_read i parent units block g live count spectator x y acts kept⟩

open Fallback in
/-- Choose the scheduled child branch and correct the returned columns with the caller's pivots. -/
noncomputable def weightedOrdinaryProgram [M8.Machine.Net] {P U : Type} {T : ℕ}
    (caller : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ caller j) (r g : ℕ) (f : P) : Pr P T columnCapacity prime U :=
  let placement := correctionColumnPlacement caller work apart
  let ports := columnPorts.trans placement
  let bank := columnBank.trans placement
  let cmp := ordinaryCutoffPorts bank (placement (Fin.last _)) (fun i => placement.injective.ne (Fin.castSucc_ne_last _))
  let pass := fun js => statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule ((r+g)+(r+g)) js)
  let is := ordinaryChildPackSchedule r g
  let emit := fun i j => let slot := correctionSlot r i j
                         readMatrixWord slot.2.val ((callerCorrectionPorts slot.1).trans caller)
  let write := LabelTraversal.sequence (fun i => LabelTraversal.sequence (emit i) (List.finRange 128)) (List.finRange 128)
  let prep := (bzero (caller 2) (caller 58) (caller 59)).seq (write.seq (bclear (caller 58)))
  let correction := (prep.seq (placedDiagonalPairs placement 127)).seq (dropWords (bank 2) (bank 34) (bank 0) (128*128))
  ((ordinaryCutoffTest cmp r).seq (.cond (fun u => symBit (u.scan (cmp 7)))
    ((pass is).seq ((Prog.call f).seq (pass is.reverse))) (pass (stoppedParentSchedule r g)))).seq correction

open Fallback RecursiveInterchangeLayout in
/-- Execute the scheduled ordinary exchange and apply the archived parent pivots. -/
theorem weightedOrdinaryChildDispatch_exec [M8.Machine.Net] {P U : Type} {T : ℕ}
    (caller : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ caller j) (body : P → Pr P T columnCapacity prime U) :
    let placement := correctionColumnPlacement caller work apart
    let ports := columnPorts.trans placement
    let cut := placement (Fin.last _)
    ∃ C : ℕ, ∀ (node : Descriptor) (i : Fin nodeChildren5.length) w (aligned : node.width = 64*(w+1)),
      let r := nodeChildren5[i.val]
      let g := 64-r
      let parent := role node 142080
      let W := CopyChildLayout.spectators parent
      0 < W →
      let d := (r+g)+(r+g)
      let M := prime^(w+1)
      let is := ordinaryChildPackSchedule r g
      let routeTime := (is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1
      let bank := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans ports
      let clean := fun (S : Stacks T prime) => ∀ k : Fin (rowSwapBlock.tapes+35), 35 ≤ k.val → S.L (ports k) = [] ∧ S.R (ports k) = []
      ∀ (v : HS T columnCapacity prime U) (S : Stacks T prime)
        (dest : ℤ → Fin 4) (q : ℤ)
        (before : Fin (M^d*W) → ZMod 2)
        (f : P) (budget cutoff L : ℕ),
      let saved := fun D : Stacks T prime => ∀ j, (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j
      let desc := ordinaryChildDescriptor r g w W
      let child := scheduledChild prime node i
      let same : rankDescriptor prime (r*(w+1)) (g*(w+1)) parent = child := by
        simp only [child,scheduledChild,aligned,Nat.mul_div_cancel_left _ (by decide : 0 < 64)]
        rfl
      let layout := (ordinaryScheduledLayout parent r g w).trans (finCongr (congrArg (volume prime) same))
      let onTape := fun (word : Fin (volume prime child) → ZMod 2) (D : Stacks T prime) =>
        ∀ z, readAt blank (D.L (bank 24)) (D.R (bank 24)) z =
          M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := desc) (word ∘ layout) z
      ∀ pivot : Fin r → (ZMod M)ˣ,
      (∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) →
      S.R (caller 55) = (List.ofFn fun k => binSyms M.size (pivot k : ZMod M).val).flatten →
      S.R (caller 56) = (List.ofFn fun k => binSyms M.size (pivot k).inv.val).flatten →
      (∀ k ∈ ([58,59,61,62,63] : List (Fin 64)), S.R (caller k) = []) →
      cutoff < 2^L → desc.width.size ≤ L →
      S.R cut = binSyms L cutoff →
      (cutoff < desc.width → child.width < node.width → ∀ word u D, onTape word D → clean D → saved D → D.R cut = binSyms L cutoff → ∃ y G t, y.user = u.user ∧ t ≤ budget ∧
        Exec body (body f) (mk u D) t (mk y G) ∧
        onTape (Shared50RecursiveNodeRows.transpose (one_dvd child.rows) word) G ∧
        (∀ j : Fin 35, j ≠ 24 → G.L (bank j) = D.L (bank j) ∧ G.R (bank j) = D.R (bank j)) ∧ clean G ∧ saved G) →
      S.R (caller 2) = binSyms M.size M → S.R (caller 53) = binSyms W.size W →
      S.R (caller 28) = binSyms 1 1 → S.R (caller 44) = binSyms M.size (1 : ZMod M).val →
      (S.R (caller 45)).length = w →
      (∀ k ∈ shearWork, S.L (work (columnBank k)) = [] ∧ S.R (work (columnBank k)) = []) →
      (∀ z, readAt blank (S.L (caller 24)) (S.R (caller 24)) (z-0) =
        RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ before)) z)) →
      (∀ z, readAt blank (S.L (caller 25)) (S.R (caller 25)) (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) →
      clean S → ∃ z F n after, z.user = v.user ∧
        n ≤ 4*w+23*desc.width+22*L+51+(if cutoff < desc.width then budget+2+2*(1+routeTime) else C*(desc.width*(M^d*W))) +
          ordinaryCorrectionTime U w W M.size W.size ∧
        Exec body (weightedOrdinaryProgram caller work apart r g f) (mk v S) n (mk z F) ∧
        (∀ (hg tg : Fin g → ZMod M) (x : IntegerMultBounds.Swap.Shear.State (Fin r) (ZMod M)) (j : Fin W),
          let address := fun y => let t := childFields hg tg y
                                  FlatCoordinateLayout.index (Fin.append t.1 t.2) j
          after (address (Weighted.child r (fun k => (pivot k : ZMod M)) (fun k => (pivot k).inv) x)) = before (address x)) ∧
        (∀ z, RadixToBinary.binaryEncoding.encode (putWord (fun _ => blank) 0 (List.ofFn (SparseRoleCircuit.encode ∘ after)) z) =
          readAt blank (F.L (caller 24)) (F.R (caller 24)) (z-0)) ∧ clean F ∧ F.R cut = binSyms L cutoff ∧
        (∀ j : Fin 64, (∀ k, correctionCallerSlots k ≠ j) → F.L (caller j) = S.L (caller j) ∧ F.R (caller j) = S.R (caller j)) ∧
        (∀ j, (∀ k, placement k ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ c, Fast.Main.mnProgPush (weightedOrdinaryProgram (U := U) caller work apart r g f) ≤ c →
          (∀ f, Fast.Main.mnProgPush (body f) ≤ c) → StackGrowthExcept (caller 24) S F
            (c*((if cutoff < desc.width then 2*(1+routeTime) else C*(desc.width*(M^d*W))) +
              ordinaryCorrectionTime U w W M.size W.size)) := by
  intro placement ports cut
  obtain ⟨C,dispatch⟩ := ordinaryChildDispatch_exec placement body
  refine ⟨C,?_⟩
  intro node i w aligned r g parent W hW d M is routeTime bank clean v S dest q before f budget cutoff L
    saved desc child eqn layout onTape pivot empty pos inv fresh cutFits widthFits cutWord recurse modulus width one padded clock temps src dst free
  let weight := fun k : Fin (r+g) => if h : k.val < r then pivot ⟨k.val,h⟩ else 1
  let input := fun x : Fin d → ZMod M => (fun k : Fin (r+g) => x (k.castAdd (r+g)),fun k : Fin (r+g) => x (k.natAdd (r+g)))
  let record := S.R (caller 60)
  have start : ColumnRecordReady bank M.size W.size record SparseRoleCircuit.encode (fun _ => blank) dest 0 q before
      (fun x => Fin.append (input x).1 (input x).2) S := by
    refine ⟨before,correctionRecordEntry caller work apart M.size W.size d dest q S before modulus width one padded clock temps src dst,?_⟩
    intro x j
    exact congrArg (fun y => before (FlatCoordinateLayout.index y j)) (Fin.append_castAdd_natAdd (f := x))
  obtain ⟨u,D,t,user,paid,run,plain,scratch,frame,_,routeGrowth⟩ := dispatch node i w aligned hW v S record dest q before input f budget cutoff L
    cutFits widthFits cutWord recurse start free
  have rankBound : r ≤ 42 := nodeChildren5_le i
  have dim : r+g = 64 := by dsimp only [g]; omega
  obtain ⟨z,F,n,same,cost,done,weighted,clear,lastWord,callerFrame,off,correctionGrowth⟩ :=
    dispatchedCorrection_exec caller work apart dim (Nat.le_add_right r g) pivot M.size W.size
      (Nat.lt_size_self _) (Nat.lt_size_self _) hW body v S _ u D t record dest q empty before input
      pos inv fresh user run frame plain scratch
  obtain ⟨after,action,returned⟩ := weightedColumn_return bank M.size W.size record dest q F before
    (fun k => (weight k : ZMod M)) (fun k => (weight k).inv) weighted
  have payload : bank 24 = caller 24 := correctionColumnPlacement_shared caller work apart 1
  refine ⟨z,F,n,after,same,cost.trans (Nat.add_le_add_right paid _),done,?_,payload ▸ returned,clear,lastWord.trans cutWord,callerFrame,off,?_⟩
  · simpa only [weight,Fin.val_castAdd,Fin.isLt,dif_pos] using action
  · intro c hp hb j ne
    obtain ⟨branch,correct⟩ := max_le_iff.mp hp
    obtain ⟨active,stopped⟩ := max_le_iff.mp (max_le_iff.mp branch).2
    obtain ⟨enter,callExit⟩ := max_le_iff.mp active
    have route := routeGrowth c enter (max_le_iff.mp callExit).2 stopped hb
    have final := correctionGrowth c correct hb
    have together := route.trans final j (payload ▸ ne)
    change n ≤ t+ordinaryCorrectionTime U w W M.size W.size at cost
    have bound : n-t ≤ ordinaryCorrectionTime U w W M.size W.size := by omega
    have price := Nat.mul_le_mul_left c bound
    rw [Nat.mul_add]
    exact ⟨together.1.trans (Nat.add_le_add_left (Nat.add_le_add_left price _) _),
      together.2.trans (Nat.add_le_add_left (Nat.add_le_add_left price _) _)⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
