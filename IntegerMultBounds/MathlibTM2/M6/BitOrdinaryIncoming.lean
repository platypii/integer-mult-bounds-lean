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
  obtain ⟨u,D,n,user,time,run,_,payload,clear,frame⟩ := ordinaryIncomingPack_exec
    (r := r) (g := g) ports body v S _ dest q hW before layout clean
  refine ⟨u,D,n,user,time,run,?_,clear,frame⟩
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
      (∀ k, 35 ≤ k.val → D.L (ports k) = [] ∧ D.R (ports k) = []) ∧
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
  obtain ⟨y,F,k,hu,hk,run,payload,clear,kept⟩ := ordinaryHeadPack_exec (r := r) (g := g)
    bank work apart body (stateLiftUp cap u) D parent target q hW before mid
    ((keep 44 (by decide)).trans one) ((congrArg List.length (keep 45 (by decide))).trans clock) (by
      intro i
      obtain ⟨left,right⟩ := outside _ (fun j => (apart _ j).symm)
      exact ⟨left.trans (free i).1,right.trans (free i).2⟩)
  have lifted := stateLift_exec_normalized cap (by decide) Empty.elim (body' := body) (fun f => nomatch f) v first
  refine ⟨y,F,_,before,hu.trans user,Nat.add_le_add (Nat.add_le_add_left time 1) hk,
    Exec.seq lifted run,payload,payload_prefix_of_read _ _ _ _ _ payload,clear,?_,action⟩
  intro j off unused
  exact ⟨(kept j unused).1.trans (outside j off).1,(kept j unused).2.trans (outside j off).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
