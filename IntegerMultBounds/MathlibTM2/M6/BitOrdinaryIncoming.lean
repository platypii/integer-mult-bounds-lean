module

public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryCall
public import IntegerMultBounds.MathlibTM2.Cover.FallbackGoodRecordRun

/-! Pack an ordinary directory row on the same tapes used by the incoming transform. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Cover.Fallback Stack Host
open CrossWeightLayout HeadPivotLayout HeadWidthLayout GoodChildLayout
open Shared50ModularControl (prime)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos Shared50ModularControl.prime_prime.pos _).ne'⟩

/-- Scalar headers reused when the scanner advances the two archives. -/
structure OrdinaryRowHeaders {T : ℕ} (bank : Fin 64 ↪ Fin T) (w W : ℕ) (S : Stacks T prime) : Prop where
  modulus : S.R (bank 2) = binSyms (prime^(w+1)).size (prime^(w+1))
  width : S.R (bank 53) = binSyms W.size W
  one : S.R (bank 28) = binSyms 1 1
  padded : S.R (bank 44) = binSyms (prime^(w+1)).size (1 : ZMod (prime^(w+1))).val
  clock : (S.R (bank 45)).length = w

theorem ordinaryHeadPack_exec [M8.Machine.Net] {P U : Type} {T r g w W : ℕ}
    (bank : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ bank j) (body : P → Pr P T columnCapacity prime U)
    (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (weights : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ) (hW : 0 < W) :
    let M := prime^(w+1)
    let d := (r+g)+(r+g)
    let full := (Fin.castLEEmb (by decide : 58 ≤ 64)).trans bank
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let ordinary := ordinaryHead.trans (adapterBank.trans machine)
    let ports := columnPorts.trans (correctionColumnPlacement bank work apart)
    let is := ordinaryChildPackSchedule r g
    ∀ before : Fin (M^d*W) → ZMod 2,
    HeadColumnReady (d := d) (W := W) ((coeff false).trans ordinary) (shear.trans ordinary)
      M.size W.size [] weights [] SparseRoleCircuit.encode (fun _ => blank) dest 0 q before S →
    S.R (bank 44) = binSyms M.size (1 : ZMod M).val → (S.R (bank 45)).length = w →
    (∀ i, S.L (work (Fin.castSucc i)) = [] ∧ S.R (work (Fin.castSucc i)) = []) →
    ∃ u D n, u.user = v.user ∧
      n ≤ 1+((is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim d i (i+1) w W M.size W.size)).sum+1) ∧
      Exec body (statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule d is))
        (mk v S) n (mk u D) ∧ RecordPayload (bank 24) (fun _ => blank) 0
          (before ∘ ordinaryRecursivePosition r g w W) D ∧
      OrdinaryRowHeaders bank w W D ∧
      (∀ k, 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []) ∧
      ∀ j, (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j := by
  intro M d full machine ordinary ports is before mid padded clock free
  have layout := correctionRecordEntry bank work apart M.size W.size d dest q S before
    mid.base mid.width mid.one padded clock (fun i _ => free _) (fun z => (mid.src z).symm)
    (fun z => (mid.dst z).symm)
  have clean (k : Fin (rowSwapBlock.tapes+35)) (hk : 35 ≤ k.val) :
      S.L (ports k) = [] ∧ S.R (ports k) = [] := by
    have off : ¬ ∃ j, columnBank (correctionColumnSlots j) = columnPorts k := by
      rintro ⟨j,h⟩
      have val := congrArg Fin.val h
      change (correctionColumnSlots j).val = k.val at val
      omega
    have eq : ports k = work (columnPorts k) := by
      change sharedRegisterPlacement work (correctionCallerSlots.trans bank) correctionRole (columnPorts k) = _
      unfold sharedRegisterPlacement
      rw [show correctionRole (columnPorts k) = none from dite_eq_right off]
    rw [eq]
    exact free k
  obtain ⟨u,D,n,user,time,run,stored,payload,clear,frame⟩ := ordinaryIncomingPack_exec
    (r := r) (g := g) ports body v S _ dest q hW before layout clean
  let col := columnBank.trans (correctionColumnPlacement bank work apart)
  have share (k : Fin 8) : col (correctionColumnSlots k) = bank (correctionCallerSlots k) :=
    correctionColumnPlacement_shared bank work apart k
  have headers : OrdinaryRowHeaders bank w W D :=
    ⟨(share 0) ▸ stored.modulus,(share 3) ▸ stored.width,(share 7) ▸ stored.one,
      (share 4) ▸ stored.padded,(share 5) ▸ stored.clock⟩
  refine ⟨u,D,n,user,time,run,?_,headers,clear,frame⟩
  intro z
  rw [sub_zero]
  have read := payload z
  change readAt blank (D.L ((columnBank.trans (correctionColumnPlacement bank work apart)) 24))
    (D.R ((columnBank.trans (correctionColumnPlacement bank work apart)) 24)) z = _ at read
  rw [show (columnBank.trans (correctionColumnPlacement bank work apart)) 24 = bank 24 from
    correctionColumnPlacement_shared bank work apart 1] at read
  simpa only [swap_source_word,List.map_ofFn] using read

open IntegerMultBounds.Swap.Shear GoodForm FlatCoordinateLayout LabelTraversal Matrix M8.Exchange M8.ReversedExchange

/-- Transform and pack one ordinary row. The witness retains the incoming
matrix action needed to interpret the recursive result on the return scan. -/
theorem ordinaryDirectoryIncoming_exec [M8.Machine.Net] {P U : Type} {T r g w W : ℕ}
    (bank : Fin 64 ↪ Fin T) (work : Fin ((rowSwapBlock.tapes+35)+1) ↪ Fin T)
    (apart : ∀ i j, work i ≠ bank j) (body : P → Pr P T columnCapacity prime U)
    (v : HS T columnCapacity prime U) (S : Stacks T prime) (hW : 0 < W) :
    let m := r+g
    let hr : r ≤ m := Nat.le_add_right ..
    let M := prime^(w+1)
    let H := M.size
    let J := W.size
    let full := (Fin.castLEEmb (by decide : 58 ≤ 64)).trans bank
    let machine := GoodChildLayout.parent.trans (parentWithWeights.trans full)
    let adapter := adapterBank.trans machine
    let host := head.trans adapter
    let c := child.trans host
    let ports := columnPorts.trans (correctionColumnPlacement bank work apart)
    let is := ordinaryChildPackSchedule r g
    ∀ (G : Matrix (Fin m) (Fin m) (ZMod M))
      (minor : ∀ j (hj : j < r), IsUnit (lead (j+1) (lt_of_lt_of_le hj hr) G).det)
      (L : Matrix (Fin m) (Fin r) (ZMod M)) (R : Matrix (Fin r) (Fin m) (ZMod M))
      (weights inv : Fin m → ZMod M) (tail dest rest invRest pivotTail : List (Fin (prime+4)))
      (target : ℤ → Fin 4) (q : ℤ) (word : Fin (M^(m+m)*W) → ZMod 2),
    let words := fun j => if hj : j ≤ r then matrixWords prime H (stageAt G r hr minor j hj).M else []
    let stage := stageAt G r hr minor r le_rfl
    let piv := fun j : Fin r => stage.M (j.castLE hr) (j.castLE hr)
    let parent := (List.ofFn fun i => binSyms H (weights i).val).flatten ++ rest
    G*G = G → G = L*R → (∀ i, weights i * inv i = 1) →
    (∀ z, q ≤ z → z < q+(M^(m+m)*W : ℕ) → target z = blank) →
    HeadColumnReady (d := m+m) (W := W) ((coeff true).trans host) (entry.trans adapter)
      H J [] parent [] SparseRoleCircuit.encode (fun _ => blank) target 0 q word S →
    S.R (adapter 27) = [] → S.R (machine 54) = (List.ofFn fun j => binSyms H (inv j).val).flatten ++ invRest →
    (S.R (host 49),S.R (host 50)) = matrixArchive words (words 0 ++ tail) dest r →
    (S.R (host 51)).length = m*m*H →
    S.R (c 18) = (List.ofFn fun j => binSyms H (piv j).val).flatten ++ pivotTail →
    S.R (c 15) = binSyms H (1 : ZMod M).val → (S.R (c 16)).length = w →
    (∀ j : Fin 20, (j ≤ 14 ∧ j ≠ 4) ∨ j = 17 → S.R (c j) = []) →
    (∀ i, S.L (work (Fin.castSucc i)) = [] ∧ S.R (work (Fin.castSucc i)) = []) →
    let cap : 217 ≤ columnCapacity := le_max_left ..
    let incoming := (stateLiftNormalize cap (by decide)).seq
      (stateLiftPr cap (by decide) Empty.elim (goodIncoming prime r hr machine))
    let pack := statePlacedNormalized ports swapStates_fit swapStates_pos Empty.elim (packSchedule (m+m) is)
    ∃ u D n before, u.user = v.user ∧
      n ≤ 1+goodIncomingTime (A := prime) (U := U) Empty.elim machine prime w W H J r hr +
        (1+((is.map (fun i => completeSwapTime (P := Empty) (U := U) Empty.elim (m+m) i (i+1) w W H J)).sum+1)) ∧
      Exec body (incoming.seq pack) (mk v S) n (mk u D) ∧
      RecordPayload (bank 24) (fun _ => blank) 0 (before ∘ ordinaryRecursivePosition r g w W) D ∧
      D.R (bank 24) = payloadWord (SparseRoleCircuit.encode ∘ before ∘ ordinaryRecursivePosition r g w W) ++
        (D.R (bank 24)).drop (RecursiveInterchangeLayout.volume prime (ordinaryChildDescriptor r g w W)) ∧
      OrdinaryRowHeaders bank w W D ∧
      (∀ k, 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []) ∧
      (∀ j : Fin 64, 29 ≤ j.val → (∀ k, correctionCallerSlots k ≠ j) →
        D.L (bank j) = S.L (bank j) ∧ D.R (bank j) = S.R (bank j)) ∧
      (∀ j, (∀ i, bank i ≠ j) → (∀ i, ports i ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) ∧
      let δ := fun t : Fin m => if t.val < r then stage.M t t else 1
      let δ' := fun t : Fin m => if t.val < r then Ring.inverse (stage.M t t) else 1
      let K := kMat (pivotMatrix (revPivots m r))
        (rev m * stage.U * rev m * rev m * (stage.L * diagonal δ)) * diagonal (fun t => inv t * δ' t)
      let action := diagonal weights * stage.L' * diagonal inv
      ∀ x y j, before (index (Fin.append (action.mulVec x)
        ((rev m * stage.U * rev m).mulVec y + K.mulVec (action.mulVec x))) j) = word (index (Fin.append x y) j) := by
  intro m hr M H J full machine adapter host c ports is G minor L R weights inv tail dest rest invRest
    pivotTail target q word words stage piv parent idem factor inverse empty initial fresh stored archive count
    pivots one clock scratch free cap incoming pack
  obtain ⟨u,D,l,before,user,time,first,mid,_,frame,action⟩ := goodIncoming_exec (P := Empty)
    Empty.elim machine G r hr minor idem L R factor weights inv inverse Shared50ModularControl.prime_prime H J
    (Nat.size_le.mp le_rfl) (Nat.size_le.mp le_rfl) hW tail dest rest invRest pivotTail SparseRoleCircuit.encode
    (fun _ => blank) target 0 q empty (stateLiftDown (by decide : 0 < 217) v) S word initial fresh stored
    archive count pivots one clock scratch
  have outside (j : Fin T) (off : ∀ i, bank i ≠ j) := frame j (fun _ => off _) (fun _ => off _)
  have keep (j : Fin 58) (hj : 29 ≤ j ∧ j ≠ 53) : D.R (full j) = S.R (full j) :=
    (frame _ (fun i => full.injective.ne ((by decide : ∀ i (j : Fin 58), 29 ≤ j → j ≠ 53 →
      parentWithWeights (GoodChildLayout.parent (adapterBank (head (shear i)))) ≠ j) i j hj.1 hj.2))
      (fun i => full.injective.ne ((by decide : ∀ i (j : Fin 58), 29 ≤ j → j ≠ 53 →
      parentWithWeights (GoodChildLayout.parent (adapterBank (entry i))) ≠ j) i j hj.1 hj.2))).2
  obtain ⟨y,F,k,hu,hk,run,payload,headers,clear,kept⟩ := ordinaryHeadPack_exec (r := r) (g := g)
    bank work apart body (stateLiftUp cap u) D parent target q hW before mid
    ((keep 44 (by decide)).trans one) ((congrArg List.length (keep 45 (by decide))).trans clock) (by
      intro i
      obtain ⟨left,right⟩ := outside _ (fun j => (apart _ j).symm)
      exact ⟨left.trans (free i).1,right.trans (free i).2⟩)
  have lifted := stateLift_exec_normalized cap (by decide) Empty.elim (body' := body) (fun f => nomatch f) v first
  refine ⟨y,F,_,before,hu.trans user,Nat.add_le_add (Nat.add_le_add_left time 1) hk,
    Exec.seq lifted run,payload,payload_prefix_of_read _ _ _ _ _ payload,headers,clear,?_,?_,action⟩
  · intro j hj off
    have outsideHead : ∀ i, (shear.trans host) i ≠ bank j := fun i => bank.injective.ne
      ((by decide : ∀ i (j : Fin 64), 29 ≤ j.val → ∀ (_ : ∀ k, correctionCallerSlots k ≠ j),
        ((Fin.castLEEmb (by decide : 58 ≤ 64)) (parentWithWeights (GoodChildLayout.parent
          (adapterBank (head (shear i)))))) ≠ j) i j hj off)
    have outsideTail : ∀ i, (entry.trans adapter) i ≠ bank j := fun i => bank.injective.ne
      ((by decide : ∀ i (j : Fin 64), 29 ≤ j.val → ∀ (_ : ∀ k, correctionCallerSlots k ≠ j),
        ((Fin.castLEEmb (by decide : 58 ≤ 64)) (parentWithWeights (GoodChildLayout.parent
          (adapterBank (entry i))))) ≠ j) i j hj off)
    have first := frame (bank j) outsideHead outsideTail
    have last := kept (bank j) (fun i => correctionColumnPlacement_off bank work apart j off (columnPorts i))
    exact ⟨last.1.trans first.1,last.2.trans first.2⟩
  intro j off unused
  exact ⟨(kept j unused).1.trans (outside j off).1,(kept j unused).2.trans (outside j off).2⟩

/-- At the end of a live incoming pass the scalar headers and the preserved
caller tapes reestablish the directory invariant once private cleanup finishes.
The pending label is consumed by the subsequent archive advance. -/
theorem directoryReady_afterIncoming {K m w W : ℕ} {v : RecursiveInterchangeLayout.Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {tail : List (Fin (prime+4))}
    {schedules : List ℕ → List (Fin (prime+4))} {pending : List ℕ} {S F : Stacks (66+K) prime} :
    let caller := Fin.castAddEmb (n := 66) K
    let bank := (Fin.castLEEmb (by decide : 64 ≤ 66)).trans caller
    let ready := DirectoryReady v proj w W (prime^(w+1)).size W.size parent prefixes tail schedules
    ready S pending → OrdinaryRowHeaders bank w W F →
    (∀ j : Fin 64, 29 ≤ j.val → j.val < 58 → (∀ k, correctionCallerSlots k ≠ j) → F.R (bank j) = S.R (bank j)) →
    (∀ i, 58 ≤ i.val → F.L i = [] ∧ F.R i = []) → ready F pending := by
  intro caller bank ready start headers keep free
  obtain ⟨directory,widths,_,scratch,projector,_,_,_,inputs,_,_,archive,queue⟩ := start
  obtain ⟨suffix,stored⟩ := projector
  have shared (j : Fin 64) (hj : j ∈ ([46,47,48,49,54,55] : List (Fin 64))) :=
    keep j ((by decide : ∀ j ∈ ([46,47,48,49,54,55] : List (Fin 64)), 29 ≤ j.val) j hj)
      ((by decide : ∀ j ∈ ([46,47,48,49,54,55] : List (Fin 64)), j.val < 58) j hj)
      ((by decide : ∀ j ∈ ([46,47,48,49,54,55] : List (Fin 64)), ∀ k, correctionCallerSlots k ≠ j) j hj)
  refine ⟨(shared 46 (by decide)).trans directory,fun j hj =>
    (congrArg List.length (shared 47 (by decide))).trans (widths j hj),free,
    (shared 49 (by decide)).trans scratch,⟨suffix,(shared 48 (by decide)).trans stored⟩,
    headers.modulus,headers.one,headers.width,?_,headers.padded,headers.clock,
    (shared 55 (by decide)).trans archive,(shared 54 (by decide)).trans queue⟩
  intro i
  let slot (i : Fin 6) := (i.natAdd 33).castLE (by decide : 39 ≤ 64)
  exact (keep (slot i) (by change 29 ≤ 33+i.val; omega) (by change 33+i.val < 58; omega)
    ((by decide : ∀ i k, correctionCallerSlots k ≠ (i.natAdd 33 : Fin (33+6)).castLE (by decide : 39 ≤ 64)) i)).trans (inputs i)

/-- Clear the live row's private tapes and recover the scanner at the same
label. All public tape heads and their stacks survive cleanup. -/
theorem ordinaryDirectoryCleanup_exec {P U : Type} {K m w W Q : ℕ} {v : RecursiveInterchangeLayout.Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {tail : List (Fin (prime+4))}
    {schedules : List ℕ → List (Fin (prime+4))} {pending : List ℕ}
    (body : P → Pr P (66+K) Q prime U) (u : HS (66+K) Q prime U) (S D : Stacks (66+K) prime) :
    let bank := (Fin.castLEEmb (by decide : 64 ≤ 66)).trans (Fin.castAddEmb K)
    let ready := DirectoryReady v proj w W (prime^(w+1)).size W.size parent prefixes tail schedules
    let work := (List.finRange (66+K)).filter (fun i => 58 ≤ i.val)
    ready S pending → OrdinaryRowHeaders bank w W D →
    (∀ j : Fin 64, 29 ≤ j.val → j.val < 58 → (∀ k, correctionCallerSlots k ≠ j) → D.R (bank j) = S.R (bank j)) →
    ∃ z F, z.user = u.user ∧ Exec body (clearWorkTapes work) (mk u D)
      ((work.map fun i => 4*(D.L i).length+2*(D.R i).length+4).sum+1) (mk z F) ∧
      ready F pending ∧ ∀ i, i.val < 58 → F.L i = D.L i ∧ F.R i = D.R i := by
  intro bank ready work start headers keep
  obtain ⟨z,user,run⟩ := clearWorkTapes_exec body work ((List.nodup_finRange _).filter _) u D
  let F : Stacks (66+K) prime := {D with L := fun i => if i ∈ work then [] else D.L i,
                                         R := fun i => if i ∈ work then [] else D.R i}
  have unchanged (i : Fin (66+K)) (hi : i.val < 58) : F.L i = D.L i ∧ F.R i = D.R i := by
    simp [F,work,Nat.not_le_of_lt hi]
  have right (j : Fin 64) (small : j.val < 58) := (unchanged (bank j) small).2
  refine ⟨z,F,user,run,directoryReady_afterIncoming start ?_ ?_ ?_,unchanged⟩
  · exact ⟨(right 2 (by decide)).trans headers.modulus,(right 53 (by decide)).trans headers.width,
      (right 28 (by decide)).trans headers.one,(right 44 (by decide)).trans headers.padded,
      (congrArg List.length (right 45 (by decide))).trans headers.clock⟩
  · exact fun j hj small off => (right j small).trans (keep j hj small off)
  · intro i hi
    simp [F,work,hi]

/-- Finish a live incoming row at the next directory boundary. The bound
charges temporary stack growth only during the local row program. -/
theorem ordinaryDirectoryAdvance_exec {P U : Type} {K m w W Q N : ℕ} {v : RecursiveInterchangeLayout.Descriptor}
    {proj : Matrix (Fin m) (Fin m) ℚ} {parent : Fin m → ZMod (prime^(w+1))}
    {prefixes : ℕ → List (Fin (prime+4))} {tail : List (Fin (prime+4))}
    {schedules : List ℕ → List (Fin (prime+4))} {j : ℕ} {js : List ℕ}
    (body : P → Pr P (66+K) Q prime U) (prog : Pr P (66+K) Q prime U)
    (u y : HS (66+K) Q prime U) (S D : Stacks (66+K) prime) (n c : ℕ) (word : Fin N → ZMod 2) :
    let caller := Fin.castAddEmb (n := 66) K
    let bank := (Fin.castLEEmb (by decide : 64 ≤ 66)).trans caller
    let ready := DirectoryReady v proj w W (prime^(w+1)).size W.size parent prefixes tail schedules
    let work := (List.finRange (66+K)).filter (fun i => 58 ≤ i.val)
    let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
    let scan := ((goodRecordScanPorts.trans slots).trans (Fin.castAddEmb 8)).trans caller
    let advance := readWithSuccessorClock (scan 1) (advanceDirectory m scan)
    y.user = u.user → Exec body prog (mk u S) n (mk y D) →
    Fast.Main.mnProgPush prog ≤ c → (∀ f, Fast.Main.mnProgPush (body f) ≤ c) →
    ready S (j::js) → schedules (j::js) = schedules js → OrdinaryRowHeaders bank w W D →
    (∀ k : Fin 64, 29 ≤ k.val → k.val < 58 → (∀ i, correctionCallerSlots i ≠ k) → D.R (bank k) = S.R (bank k)) →
    RecordPayload (caller 24) (fun _ => blank) 0 word D →
    ∃ z F t, z.user = u.user ∧
      t ≤ n+(4*work.length+1+work.length*(6*(c*n)))+(1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1)) ∧
      Exec body ((prog.seq (clearWorkTapes work)).seq advance) (mk u S) t (mk z F) ∧
      ready F js ∧ RecordPayload (caller 24) (fun _ => blank) 0 word F ∧
      ∀ k : Fin 66, k.val < 58 → k ≠ 46 → F.L (caller k) = D.L (caller k) ∧ F.R (caller k) = D.R (caller k) := by
  intro caller bank ready work slots scan advance user run push calls start skip headers keep payload
  obtain ⟨b,B,hb,clean,readyB,publicFrame⟩ := ordinaryDirectoryCleanup_exec body y S D start headers keep
  obtain ⟨z,hz,step,done⟩ := DirectoryReady.advancePadding body b readyB skip
  have growth := cleanup_cost_le work run push calls
  have cost : (work.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum = 4*work.length := by
    have each (i) (hi : i ∈ work) := start.2.2.1 i (by simpa [work] using hi)
    rw [List.map_congr_left (g := fun _ => 4) (fun i hi => by simp [(each i hi).1,(each i hi).2])]
    simp [Nat.mul_comm]
  rw [cost] at growth
  refine ⟨z,_,_,hz.trans (hb.trans user),Nat.add_le_add_right (Nat.add_le_add_left growth n) _,
    Exec.seq (Exec.seq run clean) step,done,?_,?_⟩
  · intro a
    have frame := publicFrame (caller 24) (by decide : 24 < 58)
    change readAt blank (B.L (caller 24)) (Function.update B.R (caller 46) (js.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail) (caller 24)) _ = _
    rw [Function.update_of_ne (caller.injective.ne (by decide : (24 : Fin 66) ≠ 46)),frame.1,frame.2]
    exact payload a
  · intro k hk off
    change _ ∧ Function.update B.R (caller 46) (js.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail) (caller k) = _
    rw [Function.update_of_ne (caller.injective.ne off)]
    exact publicFrame (caller k) hk

/-- On a padding row the physical scan advances both archives. Its projected
bank changes only at the directory port, leaving the payload and selectors
available to the collector. -/
theorem ordinaryPaddingArchives_exec {K T m d w W J Q : ℕ} {P F U : Type}
    (data : ScanData m d w W) (v : RecursiveInterchangeLayout.Descriptor)
    (proj : Matrix (Fin m) (Fin m) ℚ) (parent : Fin m → ZMod (prime^(w+1)))
    (prefixes : ℕ → List (Fin (prime+4))) (tail : List (Fin (prime+4)))
    (schedules : List ℕ → List (Fin (prime+4))) (j : ℕ) (js : List ℕ)
    (inside : j < data.records) (skip : schedules (j::js) = schedules js)
    (bank : Fin (66+K) ↪ Fin T) (archive : Fin T) (apart : ∀ i, bank i ≠ archive)
    (labels : P → F) (body : P → Pr P (66+K) Q prime U) (host : F → Pr F T Q prime U)
    (calls : ∀ f, host (labels f) = embProg bank labels (body f)) (u : HS T Q prime U) (S : Stacks T prime) :
    let caller := Fin.castAddEmb (n := 66) K
    let slots : Fin 7 ↪ Fin 58 := ⟨![45,46,2,47,48,44,49],by decide⟩
    let scan := ((goodRecordScanPorts.trans slots).trans (Fin.castAddEmb 8)).trans caller
    let ready := DirectoryReady v proj w W data.H J parent prefixes tail schedules
    let rest := js.flatMap (LabelDirectory.entry prefixes m (w+1)) ++ tail
    let A := embStk bank S
    ready A (j::js) → S.R archive = data.matrices j →
    ∃ z B, z.user = u.user ∧ ready (embStk bank B) js ∧ B.R archive = data.matrices (j+1) ∧
      embStk bank B = {A with R := Function.update A.R (caller 46) rest} ∧
      (∀ k, (∀ i, bank i ≠ k) → B.L k = S.L k ∧ (k ≠ archive → B.R k = S.R k)) ∧
      Exec host ((embProg bank labels (readWithSuccessorClock (scan 1) (advanceDirectory m scan))).seq
          (dropWords (bank (caller 2)) archive (bank (caller 59)) ((d+1)*(d+1))))
        (mk u S) ((1+(4*(prefixes j).length+4+(m*m*(4*(w+1)+4)+1)+1))+((d+1)*(d+1)*(4*data.H+4)+1))
        (mk z B) := by
  intro caller slots scan ready rest A start queue
  obtain ⟨y,user,run,done⟩ := DirectoryReady.advancePadding body (embDn bank u) start skip
  obtain ⟨z,B,hz,eqn,matrix,frame,advance⟩ := data.advanceEmbeddedRecord_exec j inside bank archive apart
    (caller 2) (caller 59) (caller.injective.ne (by decide)) labels body host calls _ u S y _ _ run
    (by rw [done.2.2.2.2.2.1,length_binSyms]) (done.2.2.1 _ (by decide : 58 ≤ 59)).2 queue
  exact ⟨z,B,hz.trans user,eqn ▸ done,matrix,eqn,frame,advance⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
